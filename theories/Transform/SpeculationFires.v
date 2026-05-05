From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile SpeculationGen.
Import Term.Syntax.
Import ListNotations.
Set Default Proof Using "Type".

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(** Does speculation fire on a pair where AU fails? *)

(** Pair: a config with extra free vars that a subterm doesn't depend on *)
Definition j_with_f : Supercompile.config :=
  Supercompile.canon_config
    (Typing.Typing.Cyclic.jTy
       [ListNat.list_ty; ListNat.nat2nat]
       (tApp ListNat.length (tApp (tApp ListNat.map (tVar 1)) (tVar 0)))
       Examples.nat_ty).

Definition j_without_f : Supercompile.config :=
  Supercompile.canon_config
    (Typing.Typing.Cyclic.jTy
       [ListNat.list_ty]
       (tApp ListNat.length (tVar 0))
       Examples.nat_ty).

Lemma fv_differ :
  SpeculationGen.config_fv j_with_f <> SpeculationGen.config_fv j_without_f.
Proof. vm_compute. intro H. inversion H. Qed.

Lemma dropped_nonempty :
  SpeculationGen.dropped_vars j_with_f j_without_f <> [].
Proof. vm_compute. intro H. inversion H. Qed.

Lemma au_fails :
  Supercompile.best_generalize j_with_f [(j_without_f, 0)] = None.
Proof. vm_compute. reflexivity. Qed.

Lemma speculation_fires :
  SpeculationGen.generalize_speculation j_with_f j_without_f <> None.
Proof. vm_compute. intro H. inversion H. Qed.

Lemma bgs_returns_some :
  SpeculationGen.best_generalize_with_speculation j_with_f [(j_without_f, 0)] <> None.
Proof. vm_compute. intro H. inversion H. Qed.
