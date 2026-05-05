From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  Sorting examples.

  We prove properties of insertion sort that the SC can verify
  by driving + cyclic backlinks alone — no LLM, no lemma environment.

  Each is a [_killed] lemma: two residuals computed by [vm_compute]
  and shown equal by [reflexivity].
*)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(* ------------------------------------------------------------------ *)
(** * 1. length (sort l) = length l
    Sort preserves length.  The SC should fuse sort and length into a
    single traversal that counts elements without actually sorting. *)

Definition Γ_l := [ListNat.list_ty].

Definition t_len_sort : tm :=
  tApp ListNat.length (tApp ListNat.sort (tVar 0)).

Definition t_len_id : tm :=
  tApp ListNat.length (tVar 0).

Definition r_len_sort : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_len_sort Examples.nat_ty.

Definition r_len_id : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_len_id Examples.nat_ty.

Lemma len_sort_killed :
  r_len_sort = r_len_id.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 2. length (insert x l) = succ (length l)
    Insert adds exactly one element. *)

Definition Γ_xl := [ListNat.list_ty; Examples.nat_ty].

Definition t_len_insert : tm :=
  tApp ListNat.length
       (tApp (tApp ListNat.insert (tVar 1)) (tVar 0)).

Definition t_succ_len : tm :=
  Examples.succ (tApp ListNat.length (tVar 0)).

Definition r_len_insert : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_xl
    t_len_insert Examples.nat_ty.

Definition r_succ_len : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_xl
    t_succ_len Examples.nat_ty.

Lemma len_insert_killed :
  r_len_insert = r_succ_len.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 3. sort nil = nil *)

Definition t_sort_nil : tm := tApp ListNat.sort ListNat.nil.

Lemma sort_nil :
  Supercompile.residualise_jTy 10 50 Σ [] t_sort_nil ListNat.list_ty
  = Some ListNat.nil.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 4. member x (insert x l) = true
    After inserting x, x is a member.
    This requires the SC to reason about leb being reflexive. *)

Definition t_member_insert : tm :=
  tApp (tApp ListNat.member (tVar 1))
       (tApp (tApp ListNat.insert (tVar 1)) (tVar 0)).

Definition t_true : tm := ListNat.bool_true.

Definition r_member_insert : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_xl
    t_member_insert Examples.nat_ty.

Definition r_true_const : option tm :=
  Supercompile.residualise_jTy 10 50 Σ Γ_xl
    t_true Examples.nat_ty.

Lemma member_insert_smoke :
  exists t, r_member_insert = Some t.
Proof. unfold r_member_insert. vm_compute. eexists. reflexivity. Qed.

(** Can we upgrade to exact? *)
Lemma member_insert_killed :
  r_member_insert = r_true_const.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 5. map f (sort l) smoke — SC terminates *)

Definition Γ_fl := [ListNat.list_ty; ListNat.nat2nat].

Definition t_map_sort : tm :=
  tApp (tApp ListNat.map (tVar 1)) (tApp ListNat.sort (tVar 0)).

Definition r_map_sort : option tm :=
  Supercompile.residualise_jTy_fp 4 100 300 Σ Γ_fl
    t_map_sort ListNat.list_ty.

Lemma map_sort_smoke :
  exists t, r_map_sort = Some t.
Proof. unfold r_map_sort. vm_compute. eexists. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 6. length (sort l) = length (sort (sort l))
    Sort is "length-idempotent": applying sort twice gives same length.
    Follows from len_sort_killed applied twice. *)

Definition t_len_sort_sort : tm :=
  tApp ListNat.length (tApp ListNat.sort (tApp ListNat.sort (tVar 0))).

Definition r_len_sort_sort : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_len_sort_sort Examples.nat_ty.

Lemma len_sort_sort_killed :
  r_len_sort_sort = r_len_id.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 7. sum l = sum (sort l)
    Sort preserves the sum.  This requires the SC to discover that
    insert is a permutation — hard. Try as smoke first. *)

Definition t_sum_sort : tm :=
  tApp ListNat.sum (tApp ListNat.sort (tVar 0)).

Definition t_sum_id : tm :=
  tApp ListNat.sum (tVar 0).

Definition r_sum_sort : option tm :=
  Supercompile.residualise_jTy_fp 4 100 300 Σ Γ_l
    t_sum_sort Examples.nat_ty.

Definition r_sum_id : option tm :=
  Supercompile.residualise_jTy_fp 4 100 300 Σ Γ_l
    t_sum_id Examples.nat_ty.

Lemma sum_sort_smoke :
  exists t, r_sum_sort = Some t.
Proof. unfold r_sum_sort. vm_compute. eexists. reflexivity. Qed.

Lemma sum_sort_killed :
  r_sum_sort = r_sum_id.
Proof. vm_compute. reflexivity. Qed.
