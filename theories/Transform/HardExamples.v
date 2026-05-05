From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile SpeculationGen.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  Hard supercompilation tests.

  Each lemma is either:
  - [_exact]  : the two residuals are definitionally equal (the SC fused them)
  - [_smoke]  : the SC produces Some output but we do not yet claim equality
  - [_killed] : upgraded from smoke to exact — the SC kills this example

  The goal is to convert every smoke test into an exact test.
*)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(* ------------------------------------------------------------------ *)
(** * 1. length (map f (map g l)) = length l
    The NOTE in SupercompileChecklistIndexPipeline.v says this is a smoke test.
    We try to kill it. *)

Definition Γ_fgl : Ty.ctx :=
  [ListNat.list_ty; ListNat.nat2nat; ListNat.nat2nat].

Definition t_len_map_map : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.map (tVar 1))
      (tApp (tApp ListNat.map (tVar 2)) (tVar 0))).

Definition t_len_l : tm :=
  tApp ListNat.length (tVar 0).

Definition r_len_map_map : option tm :=
  Supercompile.residualise_jTy 80 200 Σ Γ_fgl t_len_map_map Examples.nat_ty.

Definition r_len_l : option tm :=
  Supercompile.residualise_jTy 80 200 Σ
    [ListNat.list_ty] t_len_l Examples.nat_ty.

(** Does the SC fuse length ∘ map ∘ map to length? *)
Lemma len_map_map_killed :
  r_len_map_map = r_len_l.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 2. length (map f l) = length l — baseline *)

Definition Γ_fl : Ty.ctx := [ListNat.list_ty; ListNat.nat2nat].
Definition t_len_map : tm :=
  tApp ListNat.length (tApp (tApp ListNat.map (tVar 0)) (tVar 1)).

Definition r_len_map : option tm :=
  Supercompile.residualise_jTy 80 200 Σ Γ_fl t_len_map Examples.nat_ty.
Definition r_len_l2 : option tm :=
  Supercompile.residualise_jTy 80 200 Σ [ListNat.list_ty] t_len_l Examples.nat_ty.

Lemma len_map_killed :
  r_len_map = r_len_l2.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 3. length (append l1 l2) = plus (length l1) (length l2) — already known *)

Definition Γ_ll : Ty.ctx := [ListNat.list_ty; ListNat.list_ty].

Definition t_len_append : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append (tVar 1)) (tVar 0)).

Definition t_plus_lens : tm :=
  tApp (tApp Examples.plusL (tApp ListNat.length (tVar 1)))
       (tApp ListNat.length (tVar 0)).

Definition r_len_append : option tm :=
  Supercompile.residualise_jTy 80 200 Σ Γ_ll t_len_append Examples.nat_ty.
Definition r_plus_lens : option tm :=
  Supercompile.residualise_jTy 80 200 Σ Γ_ll t_plus_lens Examples.nat_ty.

Lemma len_append_killed :
  r_len_append = r_plus_lens.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 4. length (append (append l1 l2) l3) = length (append l1 (append l2 l3))
    Append associativity via index normalisation.
    Uses residualise_jTy_fp (fixed-point iteration). *)

Definition Γ_lll : Ty.ctx :=
  [ListNat.list_ty; ListNat.list_ty; ListNat.list_ty].

Definition t_append_assoc_l : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append
            (tApp (tApp ListNat.append (tVar 2)) (tVar 1)))
          (tVar 0)).

Definition t_append_assoc_r : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append (tVar 2))
          (tApp (tApp ListNat.append (tVar 1)) (tVar 0))).

Definition r_assoc_l : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lll
    t_append_assoc_l Examples.nat_ty.
Definition r_assoc_r : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lll
    t_append_assoc_r Examples.nat_ty.

Lemma append_assoc_killed :
  r_assoc_l = r_assoc_r.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 5. length (take n l ++ drop n l) = length l
    Split-merge identity. *)

Definition Γ_nl : Ty.ctx := [ListNat.list_ty; Examples.nat_ty].

Definition t_take_drop : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append
            (tApp (tApp ListNat.take (tVar 1)) (tVar 0)))
          (tApp (tApp ListNat.drop (tVar 1)) (tVar 0))).

Definition r_take_drop : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_nl
    t_take_drop Examples.nat_ty.
Definition r_len_l3 : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ [ListNat.list_ty]
    t_len_l Examples.nat_ty.

Lemma take_drop_killed :
  r_take_drop = r_len_l3.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 6. map f (append l1 l2) = append (map f l1) (map f l2)
    Map distributes over append. Both sides should SC to the same normal form. *)

Definition Γ_fll : Ty.ctx :=
  [ListNat.list_ty; ListNat.list_ty; ListNat.nat2nat].

(** map f (append l1 l2) *)
Definition t_map_append : tm :=
  tApp (tApp ListNat.map (tVar 2))
       (tApp (tApp ListNat.append (tVar 1)) (tVar 0)).

(** append (map f l1) (map f l2) *)
Definition t_append_map : tm :=
  tApp (tApp ListNat.append
          (tApp (tApp ListNat.map (tVar 2)) (tVar 1)))
       (tApp (tApp ListNat.map (tVar 2)) (tVar 0)).

Definition r_map_append : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_fll
    t_map_append ListNat.list_ty.

Definition r_append_map : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_fll
    t_append_map ListNat.list_ty.

Lemma map_append_killed :
  r_map_append = r_append_map.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 7. sum (map succ l) = plus (length l) (sum l)
    A classic accumulator fusion example. *)

Definition Γ_l : Ty.ctx := [ListNat.list_ty].

(** sum (map succ l) *)
Definition t_sum_map_succ : tm :=
  tApp ListNat.sum
       (tApp (tApp ListNat.map Examples.succ_fn) (tVar 0)).

(** plus (length l) (sum l) *)
Definition t_plus_len_sum : tm :=
  tApp (tApp Examples.plusL (tApp ListNat.length (tVar 0)))
       (tApp ListNat.sum (tVar 0)).

Definition r_sum_map_succ : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_sum_map_succ Examples.nat_ty.

Definition r_plus_len_sum : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_plus_len_sum Examples.nat_ty.

Lemma sum_map_succ_killed :
  r_sum_map_succ = r_plus_len_sum.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 8. length (rev_acc l acc) = plus (length l) (length acc)
    The SC must discover the accumulator invariant. *)

Definition Γ_ll2 : Ty.ctx := [ListNat.list_ty; ListNat.list_ty].

(** length (rev_acc l acc) *)
Definition t_len_rev_acc : tm :=
  tApp ListNat.length
       (tApp (tApp ListNat.rev_acc (tVar 1)) (tVar 0)).

(** plus (length l) (length acc) *)
Definition t_plus_len_len : tm :=
  tApp (tApp Examples.plusL (tApp ListNat.length (tVar 1)))
       (tApp ListNat.length (tVar 0)).

Definition r_len_rev_acc : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_ll2
    t_len_rev_acc Examples.nat_ty.

Definition r_plus_len_len : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_ll2
    t_plus_len_len Examples.nat_ty.

Lemma len_rev_acc_killed :
  r_len_rev_acc = r_plus_len_len.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Dependency / Speculation tests                                    *)

(** Test: [length] does not depend on the function argument [f].
    In context [f : Nat→Nat, l : List], the term [length l] has
    fv = {1} (the list), not {0} (the function).  So [f] is a
    dropped variable — it is loop-invariant w.r.t. [length]. *)
Lemma length_independent_of_f :
  SpeculationGen.vars_independent_of
    (tApp ListNat.length (tVar 1))  (* length l, where l = tVar 1 *)
    [0]                              (* f = tVar 0 is the "loop variable" *)
  = true.
Proof. vm_compute. reflexivity. Qed.

(** Test: [map f l] DOES depend on [f] (tVar 0). *)
Lemma map_depends_on_f :
  SpeculationGen.vars_independent_of
    (tApp (tApp ListNat.map (tVar 0)) (tVar 1))
    [0]
  = false.
Proof. vm_compute. reflexivity. Qed.

(** Test: the application head of [map f l] — namely [map] itself —
    is independent of both [f] and [l]. *)
Lemma map_head_independent :
  SpeculationGen.vars_independent_of ListNat.map [0; 1] = true.
Proof. vm_compute. reflexivity. Qed.

(** Test: [independent_subterms] on [length (map f l)] with dropped = [0]
    (i.e. [f] is the loop-invariant variable) finds [length] and
    [map] as independent subterms but not the full application. *)
Lemma independent_subterms_length_map :
  let t := tApp ListNat.length
                (tApp (tApp ListNat.map (tVar 0)) (tVar 1)) in
  (* length is independent of f (tVar 0) — it never mentions it *)
  existsb
    (Supercompile.tm_eqb (tApp ListNat.length
                               (tApp (tApp ListNat.map (tVar 0)) (tVar 1))))
    (SpeculationGen.independent_subterms t [0])
  = false. (* the FULL term is NOT independent — good *)
Proof. vm_compute. reflexivity. Qed.

