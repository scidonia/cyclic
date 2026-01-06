From Stdlib Require Import Utf8.

From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Judgement Require Import Typing.

Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.

(**
  CIU-style observational equivalence for *typing judgements*.

  This is the version we actually want for transformation correctness:
  - quantify over *typed* closing substitutions (`Typing.has_subst`)
  - substitutions range over **values** (standard CIU restriction)
  - observe termination to the same *value* (`Semantics.Cbn.terminates_to`)

  Intuition:
  `ciu_jTy Σ Γ t u A` means: for any well-typed value-instantiation of the
  context Γ, `t` and `u` are indistinguishable by value-observation.
*)

Definition ciu_jTy (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) : Prop :=
  (forall (Δ : Ty.ctx) (σ : list tm) (v : tm),
      Ty.has_subst Σenv Δ σ Γ ->
      Forall value σ ->
      terminates_to (Ty.subst_list σ t) v ->
      terminates_to (Ty.subst_list σ u) v)
  /\
  (forall (Δ : Ty.ctx) (σ : list tm) (v : tm),
      Ty.has_subst Σenv Δ σ Γ ->
      Forall value σ ->
      terminates_to (Ty.subst_list σ u) v ->
      terminates_to (Ty.subst_list σ t) v).

Lemma ciu_jTy_refl (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  ciu_jTy Σenv Γ t t A.
Proof.
  split; intros Δ σ v _ _ Hv; exact Hv.
Qed.

Lemma ciu_jTy_sym (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) :
  ciu_jTy Σenv Γ t u A -> ciu_jTy Σenv Γ u t A.
Proof.
  intro H.
  destruct H as [Htu Hut].
  split; assumption.
Qed.

Lemma ciu_jTy_trans (Σenv : Ty.env) (Γ : Ty.ctx) (t u w A : tm) :
  ciu_jTy Σenv Γ t u A -> ciu_jTy Σenv Γ u w A -> ciu_jTy Σenv Γ t w A.
Proof.
  intros Htu Huw.
  destruct Htu as [Htu Hut].
  destruct Huw as [Huw Hwu].
  split.
  - intros Δ σ v Hσ Hvσ Hv.
    apply Huw with (Δ := Δ) (σ := σ); [exact Hσ|exact Hvσ|].
    apply Htu with (Δ := Δ) (σ := σ); [exact Hσ|exact Hvσ|exact Hv].
  - intros Δ σ v Hσ Hvσ Hv.
    apply Hut with (Δ := Δ) (σ := σ); [exact Hσ|exact Hvσ|].
    apply Hwu with (Δ := Δ) (σ := σ); [exact Hσ|exact Hvσ|exact Hv].
Qed.

Lemma ciu_jTy_of_eq (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) :
  t = u -> ciu_jTy Σenv Γ t u A.
Proof.
  intro ->. apply ciu_jTy_refl.
Qed.
