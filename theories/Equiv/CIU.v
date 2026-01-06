From Stdlib Require Import Utf8.

From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.

Import Term.Syntax.

Set Default Proof Using "Type".

(**
  CIU-style observational equivalence for terms.

  Design choice (see `cyclic_proof_iso.md`):
  - observations are values (CBN values from `Semantics.Cbn`)
  - equivalence is CIU-style: quantify over substitutions
  - intended use assumes termination has been proved externally
*)

Definition ciu (t u : tm) : Prop :=
  (forall (σ : var -> tm) (v : tm), terminates_to (t.[σ]) v -> terminates_to (u.[σ]) v)
  /\
  (forall (σ : var -> tm) (v : tm), terminates_to (u.[σ]) v -> terminates_to (t.[σ]) v).

Lemma ciu_refl (t : tm) : ciu t t.
Proof.
  split; intros σ v Hv; exact Hv.
Qed.

Lemma ciu_sym (t u : tm) : ciu t u -> ciu u t.
Proof.
  intro H.
  destruct H as [Htu Hut].
  split; assumption.
Qed.

Lemma ciu_trans (t u w : tm) : ciu t u -> ciu u w -> ciu t w.
Proof.
  intros Htu Huw.
  destruct Htu as [Htu Hut].
  destruct Huw as [Huw Hwu].
  split.
  - intros σ v Hv. apply Huw. apply Htu. exact Hv.
  - intros σ v Hv. apply Hut. apply Hwu. exact Hv.
Qed.

Lemma ciu_of_eq (t u : tm) : t = u -> ciu t u.
Proof.
  intro ->. apply ciu_refl.
Qed.
