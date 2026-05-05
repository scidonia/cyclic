From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax. Import ListNotations.
Set Default Proof Using "Type".

(** Type-Index Trace Extension: Correctness Tests *)

(** Test 1: is_structurally_gt *)
Lemma succ_gt_zero :
  Supercompile.is_structurally_gt
    (Examples.succ (Examples.succ Examples.zero))
    Examples.zero = true.
Proof. vm_compute. reflexivity. Qed.

Lemma succ_succ_decreasing :
  Supercompile.is_structurally_gt
    (Examples.succ (Examples.succ Examples.zero))
    (Examples.succ Examples.zero) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma no_decrease_wrong_way :
  Supercompile.is_structurally_gt
    Examples.zero
    (Examples.succ Examples.zero) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma equal_not_decreasing :
  Supercompile.is_structurally_gt
    (Examples.succ Examples.zero)
    (Examples.succ Examples.zero) = false.
Proof. vm_compute. reflexivity. Qed.

(** Test 2: full build is clean — all existing theorems hold *)
