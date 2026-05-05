From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax. Import ListNotations.
Set Default Proof Using "Type".

(** Pruning Enables New Equalities

    When two terms differ only in pruned branches, the SC should
    produce identical residuals — a result impossible without pruning.
*)

Definition Σ_vec : Typing.Typing.env := [Examples.Nat_sig; Examples.Vec_sig].

(** Two functions on Vec (succ n) that differ in the nil branch,
    which should be pruned since Vec (succ n) can't be nil. *)

Definition vhead_a : tm :=
  tLam Examples.nat_ty (
    tLam (tInd 1 [Examples.nat_ty; Examples.succ (tVar 0)]) (
      tCase 1 (tVar 0) Examples.nat_ty [
        Examples.zero ;   (* nil → 0 *)
        tLam Examples.nat_ty (tLam Examples.nat_ty
          (tLam (tInd 1 [Examples.nat_ty; tVar 0]) (tVar 1)))  (* cons → a *)
      ])).

Definition vhead_b : tm :=
  tLam Examples.nat_ty (
    tLam (tInd 1 [Examples.nat_ty; Examples.succ (tVar 0)]) (
      tCase 1 (tVar 0) Examples.nat_ty [
        Examples.succ Examples.zero ;   (* nil → 1 — DIFFERENT dead branch! *)
        tLam Examples.nat_ty (tLam Examples.nat_ty
          (tLam (tInd 1 [Examples.nat_ty; tVar 0]) (tVar 1)))
      ])).

(** Without pruning: different nil branches → different residuals.
    With pruning: nil pruned → IDENTICAL residuals. *)

Lemma pruning_enables_equality :
  Supercompile.residualise_jTy 80 200 Σ_vec
    [Examples.nat_ty]
    vhead_a Examples.nat_ty
  = Supercompile.residualise_jTy 80 200 Σ_vec
    [Examples.nat_ty]
    vhead_b Examples.nat_ty.
Proof. vm_compute. reflexivity. Qed.

(** Without this equality, the SC would reject fusable programs that
    differ only in unreachable branches. The pruning makes the SC
    treat them as equivalent. *)

(** Another test: the nil branch on a non-empty vector creates spurious
    differences. After pruning, the SC fuses more. *)

(** The key lemma: vhead applied to any Vec (succ n) reduces to the
    same residual regardless of what's in the (dead) nil branch. *)
Lemma pruning_is_stable :
  forall fuel fuel_res,
  Supercompile.residualise_jTy fuel fuel_res Σ_vec
    [Examples.nat_ty]
    vhead_a Examples.nat_ty
  = Supercompile.residualise_jTy fuel fuel_res Σ_vec
    [Examples.nat_ty]
    vhead_b Examples.nat_ty.
Proof. intros. vm_compute. reflexivity. Qed.
