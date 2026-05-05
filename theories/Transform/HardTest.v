From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax.

Set Default Proof Using "Type".

(** Hard test cases for LLM-assisted supercompilation. *)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(** Test 1: Nested map fusion [length (map f (map g l))] *)
Definition len_map_map : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.map (tVar 1))
      (tApp (tApp ListNat.map (tVar 2)) (tVar 0))).

(** Test 2: Simple double-map for the SC to directly handle *)
Definition len_map : tm :=
  tApp ListNat.length (tApp (tApp ListNat.map (tVar 0)) (tVar 1)).

(** Run supercompiler and get residuals *)
Definition residual1 : option tm :=
  Supercompile.residualise_jTy 80 200 Σ
    [ListNat.list_ty; ListNat.nat2nat; ListNat.nat2nat] len_map_map Examples.nat_ty.

Definition residual2 : option tm :=
  Supercompile.residualise_jTy 80 200 Σ
    [ListNat.list_ty; ListNat.nat2nat] len_map Examples.nat_ty.

(** Smoke tests: supercompiler produces SOME output *)
Lemma residual1_ok : exists t, residual1 = Some t.
Proof. unfold residual1. vm_compute. eexists. reflexivity. Qed.

Lemma residual2_ok : exists t, residual2 = Some t.
Proof. unfold residual2. vm_compute. eexists. reflexivity. Qed.
