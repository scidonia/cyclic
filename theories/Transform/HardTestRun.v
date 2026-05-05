From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax.

Set Default Proof Using "Type".

(** Hard test: nested map fusion *)
Definition Σ := [Examples.Nat_sig; ListNat.List_sig].
Definition Γ2 := [ListNat.list_ty; ListNat.nat2nat; ListNat.nat2nat].
Definition Γ1 := [ListNat.list_ty; ListNat.nat2nat].

Definition t_nested : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.map (tVar 1))
      (tApp (tApp ListNat.map (tVar 2)) (tVar 0))).

Definition t_simple : tm :=
  tApp ListNat.length (tApp (tApp ListNat.map (tVar 0)) (tVar 1)).

(** Run supercompiler and define the result *)
Definition residual_nested : option tm :=
  Supercompile.residualise_jTy 80 200 Σ Γ2 t_nested Examples.nat_ty.

Definition residual_simple : option tm :=
  Supercompile.residualise_jTy 80 200 Σ Γ1 t_simple Examples.nat_ty.

(* To see the supercompiler output, load this file in Rocq repl and run:
     Print residual_nested.
     Print residual_simple.
   Or compute the normal form:
     Eval vm_compute in residual_nested. *)
