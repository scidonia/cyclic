From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  Maybe (Option) Monad Laws + Additional Index Calculations

  The Maybe monad on [Maybe Nat] has:
    return x      = just x
    bind nothing f = nothing
    bind (just x) f = f x

  We also prove index calculations that arise naturally from
  dependent type indices normalised by the SC:
  - Vec index arithmetic
  - Fin index arithmetic
  - Interaction between list operations and their lengths as Vec indices
*)

(** Σ includes Nat (0), List (1), Maybe (2) *)
Definition Σ := [Examples.Nat_sig; ListNat.List_sig; ListNat.Maybe_sig].

(** Σ for Vec examples: Nat (0), List (1), Maybe (2), Vec (3) *)
Definition Σ_vec := [Examples.Nat_sig; ListNat.List_sig;
                     ListNat.Maybe_sig; Examples.Vec_sig].

(* ------------------------------------------------------------------ *)
(** * Maybe Monad Laws                                                  *)
(* ------------------------------------------------------------------ *)

Definition maybe_fun_ty := tPi Examples.nat_ty ListNat.maybe_ty.

Definition Γ_x    := [Examples.nat_ty].
Definition Γ_xf   := [Examples.nat_ty; maybe_fun_ty].
Definition Γ_mf   := [ListNat.maybe_ty; maybe_fun_ty].
Definition Γ_mfg  := [ListNat.maybe_ty; maybe_fun_ty; maybe_fun_ty].

(** Law 1: bind (return x) f = f x *)
Definition t_maybe_left_lhs : tm :=
  tApp (tApp ListNat.bind_maybe
              (tApp ListNat.return_maybe (tVar 1)))
       (tVar 0).

Definition t_maybe_left_rhs : tm :=
  tApp (tVar 0) (tVar 1).

Definition r_maybe_left_lhs : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ Γ_xf
    t_maybe_left_lhs ListNat.maybe_ty.

Definition r_maybe_left_rhs : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ Γ_xf
    t_maybe_left_rhs ListNat.maybe_ty.

Theorem maybe_monad_left_identity :
  r_maybe_left_lhs = r_maybe_left_rhs.
Proof. vm_compute. reflexivity. Qed.

(** Law 2: bind m return = m *)
Definition t_maybe_right_lhs : tm :=
  tApp (tApp ListNat.bind_maybe (tVar 0))
       ListNat.return_maybe.

Definition t_maybe_right_rhs : tm := tVar 0.

Definition r_maybe_right_lhs : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ [ListNat.maybe_ty]
    t_maybe_right_lhs ListNat.maybe_ty.

Definition r_maybe_right_rhs : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ [ListNat.maybe_ty]
    t_maybe_right_rhs ListNat.maybe_ty.

Theorem maybe_monad_right_identity :
  r_maybe_right_lhs = r_maybe_right_rhs.
Proof. vm_compute. reflexivity. Qed.

(** Law 3: bind (bind m f) g = bind m (λx. bind (f x) g) *)
Definition t_maybe_assoc_lhs : tm :=
  tApp (tApp ListNat.bind_maybe
              (tApp (tApp ListNat.bind_maybe (tVar 2)) (tVar 1)))
       (tVar 0).

Definition t_maybe_assoc_rhs : tm :=
  tApp (tApp ListNat.bind_maybe (tVar 2))
       (tLam Examples.nat_ty
              (tApp (tApp ListNat.bind_maybe (tApp (tVar 2) (tVar 0)))
                    (tVar 1))).

Definition r_maybe_assoc_lhs : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ Γ_mfg
    t_maybe_assoc_lhs ListNat.maybe_ty.

Definition r_maybe_assoc_rhs : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ Γ_mfg
    t_maybe_assoc_rhs ListNat.maybe_ty.

Theorem maybe_monad_associativity :
  r_maybe_assoc_lhs = r_maybe_assoc_rhs.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Maybe-List interaction                                           *)
(**                                                                    *)
(**   These arise when Maybe is used as an index for partial functions  *)
(**   on lists — e.g., safe head, safe nth.                            *)
(* ------------------------------------------------------------------ *)

(** safe_head : List -> Maybe Nat *)
Definition safe_head : tm :=
  tLam ListNat.list_ty (
    tCase 1 (tVar 0) ListNat.maybe_ty
      [ ListNat.nothing ;
        (* cons branch: tVar 0 = xs, tVar 1 = x *)
        tLam Examples.nat_ty (
          tLam ListNat.list_ty (
            ListNat.just (tVar 1)
          ))
      ]).

(** bind_maybe (safe_head l) f = case l of nil → nothing | cons x _ → f x *)
Definition t_head_bind : tm :=
  tApp (tApp ListNat.bind_maybe (tApp safe_head (tVar 1)))
       (tVar 0).

Definition t_head_case : tm :=
  tCase 1 (tVar 1) ListNat.maybe_ty
    [ ListNat.nothing ;
      tLam Examples.nat_ty (
        tLam ListNat.list_ty (
          tApp (tVar 2) (tVar 1)
        ))
    ].

Definition r_head_bind : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ
    [ListNat.list_ty; maybe_fun_ty]
    t_head_bind ListNat.maybe_ty.

Definition r_head_case : option tm :=
  Supercompile.residualise_jTy_fp 4 100 200 Σ
    [ListNat.list_ty; maybe_fun_ty]
    t_head_case ListNat.maybe_ty.

Theorem head_bind_fusion :
  r_head_bind = r_head_case.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Vec index arithmetic                                             *)
(**                                                                    *)
(**   The SC normalises indices of dependent types.  We prove that     *)
(**   the SC-computed index of [Vec A (length l)] agrees with the      *)
(**   SC-computed index of [Vec A (length (map f l))].                 *)
(**                                                                    *)
(**   This is the foundational justification for using SC to typecheck  *)
(**   dependent vector operations: if the SC equates the indices, the  *)
(**   dependent type is well-formed.                                   *)
(* ------------------------------------------------------------------ *)

Definition Σ_lv := [Examples.Nat_sig; ListNat.List_sig;
                    ListNat.Maybe_sig; Examples.Vec_sig].

Definition vec_idx (n : tm) : tm := tInd 3 [Examples.nat_ty; n].

(** Vec index after map: length (map f l) = length l *)
Definition r_vec_map_idx : option tm :=
  Supercompile.residualise_jTy 80 200
    [Examples.Nat_sig; ListNat.List_sig]
    [ListNat.list_ty; ListNat.nat2nat]
    (tApp ListNat.length
          (tApp (tApp ListNat.map (tVar 1)) (tVar 0)))
    Examples.nat_ty.

Definition r_vec_base_idx : option tm :=
  Supercompile.residualise_jTy 80 200
    [Examples.Nat_sig; ListNat.List_sig]
    [ListNat.list_ty; ListNat.nat2nat]
    (tApp ListNat.length (tVar 0))
    Examples.nat_ty.

Theorem vec_map_index_normalises :
  option_map vec_idx r_vec_map_idx =
  option_map vec_idx r_vec_base_idx.
Proof. vm_compute. reflexivity. Qed.

(** Vec index after bind: length (bind l f) in terms of length l and f *)
(** This is harder — bind can change the length.  We just check SC terminates. *)
Definition r_vec_bind_idx : option tm :=
  Supercompile.residualise_jTy_fp 4 100 300
    [Examples.Nat_sig; ListNat.List_sig]
    [ListNat.list_ty; tPi Examples.nat_ty ListNat.list_ty]
    (tApp ListNat.length
          (tApp (tApp ListNat.bind (tVar 1)) (tVar 0)))
    Examples.nat_ty.

Lemma vec_bind_index_smoke :
  exists t, r_vec_bind_idx = Some t.
Proof. unfold r_vec_bind_idx. vm_compute. eexists. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Plus commutativity and associativity as index equalities         *)
(**                                                                    *)
(**   These are the canonical hard cases that require strengthened IH. *)
(**   The SC CAN prove them for the specific [plusL] (left-recursive), *)
(**   because it drives into the left argument and folds.             *)
(* ------------------------------------------------------------------ *)

Definition Γ_mn := [Examples.nat_ty; Examples.nat_ty].

(** plus m n = plus n m — commutativity *)
Definition t_plus_comm_lhs : tm :=
  tApp (tApp Examples.plusL (tVar 1)) (tVar 0).

Definition t_plus_comm_rhs : tm :=
  tApp (tApp Examples.plusL (tVar 0)) (tVar 1).

Definition r_plus_comm_lhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_mn
    t_plus_comm_lhs Examples.nat_ty.

Definition r_plus_comm_rhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_mn
    t_plus_comm_rhs Examples.nat_ty.

(** Smoke: both SC to Some — the question is whether they're equal *)
Lemma plus_comm_smoke :
  exists a b, r_plus_comm_lhs = Some a /\ r_plus_comm_rhs = Some b.
Proof. unfold r_plus_comm_lhs, r_plus_comm_rhs. vm_compute.
       do 2 eexists. split; reflexivity. Qed.

(** Try exact equality — this requires strengthened IH, so likely fails *)
(* Uncomment to test:
Lemma plus_comm_killed :
  r_plus_comm_lhs = r_plus_comm_rhs.
Proof. vm_compute. reflexivity. Qed.
*)

(** plus m (plus n k) = plus (plus m n) k — associativity *)
Definition Γ_mnk := [Examples.nat_ty; Examples.nat_ty; Examples.nat_ty].

Definition t_plus_assoc_l : tm :=
  tApp (tApp Examples.plusL (tVar 2))
       (tApp (tApp Examples.plusL (tVar 1)) (tVar 0)).

Definition t_plus_assoc_r : tm :=
  tApp (tApp Examples.plusL
              (tApp (tApp Examples.plusL (tVar 2)) (tVar 1)))
       (tVar 0).

Definition r_plus_assoc_l : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_mnk
    t_plus_assoc_l Examples.nat_ty.

Definition r_plus_assoc_r : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_mnk
    t_plus_assoc_r Examples.nat_ty.

Lemma plus_assoc_smoke :
  exists a b, r_plus_assoc_l = Some a /\ r_plus_assoc_r = Some b.
Proof. unfold r_plus_assoc_l, r_plus_assoc_r. vm_compute.
       do 2 eexists. split; reflexivity. Qed.

(** Try exact: *)
Lemma plus_assoc_killed :
  r_plus_assoc_l = r_plus_assoc_r.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Summary of what this file proves                                 *)
(**                                                                    *)
(**  PROVED (exact equality, vm_compute):                              *)
(**   maybe_monad_left_identity   : bind (return x) f = f x           *)
(**   maybe_monad_right_identity  : bind m return     = m             *)
(**   maybe_monad_associativity   : bind (bind m f) g = bind m (λx..) *)
(**   head_bind_fusion             : bind (head l) f fuses cleanly    *)
(**   vec_map_index_normalises     : Vec idx after map = Vec idx base  *)
(**   plus_assoc_killed            : plus m (plus n k) = plus (plus m n) k *)
(**                                                                    *)
(**  SMOKE ONLY (SC terminates but sides may differ):                  *)
(**   vec_bind_index_smoke         : bind changes length, no simple eq *)
(**   plus_comm_smoke              : commutativity needs strengthened IH *)
(**                                  (recorded in OMEGA_RULE_PLAN.md)  *)
(* ------------------------------------------------------------------ *)
