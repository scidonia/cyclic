From Stdlib Require Import List Utf8.

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

(** Relational CIU

    The basic [ciu_jTy] notion above is *extensional but intensional in the
    observed value*: it requires both terms to terminate to the *same syntactic*
    value.

    For some examples (notably, "index bureaucracy" examples where indices are
    themselves programs), it is more convenient to observe results up to a
    relation [R] rather than literal syntactic equality.

    [ciu_jTy_rel Σ Γ t u A R] means:
    under any typed closing value substitution, whenever [t] terminates to some
    value [v], then [u] terminates to some value [v'] such that [R v v'] (and
    conversely).
*)

Definition ciu_jTy_rel
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) (R : tm -> tm -> Prop) : Prop :=
  (forall (Δ : Ty.ctx) (σ : list tm) (v : tm),
      Ty.has_subst Σenv Δ σ Γ ->
      Forall value σ ->
      terminates_to (Ty.subst_list σ t) v ->
      exists v', terminates_to (Ty.subst_list σ u) v' /\ R v v')
  /\
  (forall (Δ : Ty.ctx) (σ : list tm) (v : tm),
      Ty.has_subst Σenv Δ σ Γ ->
      Forall value σ ->
      terminates_to (Ty.subst_list σ u) v ->
      exists v', terminates_to (Ty.subst_list σ t) v' /\ R v' v).

Lemma ciu_jTy_rel_mono
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm)
    (R S : tm -> tm -> Prop) :
  (forall v1 v2, R v1 v2 -> S v1 v2) ->
  ciu_jTy_rel Σenv Γ t u A R ->
  ciu_jTy_rel Σenv Γ t u A S.
Proof.
  intros HRS [Htu Hut].
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Htu Δ σ v Hσ Hvσ Hterm) as [v' [Hterm' HR]].
    exists v'. split; [exact Hterm'|exact (HRS _ _ HR)].
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Hut Δ σ v Hσ Hvσ Hterm) as [v' [Hterm' HR]].
    exists v'. split; [exact Hterm'|exact (HRS _ _ HR)].
Qed.

Lemma ciu_jTy_rel_refl
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) (R : tm -> tm -> Prop) :
  (forall v, value v -> R v v) ->
  ciu_jTy_rel Σenv Γ t t A R.
Proof.
  intros HR.
  split.
  - intros Δ σ v _Hσ _Hvσ Hterm.
    exists v. split; [exact Hterm|].
    apply HR. exact (proj2 Hterm).
  - intros Δ σ v _Hσ _Hvσ Hterm.
    exists v. split; [exact Hterm|].
    apply HR. exact (proj2 Hterm).
Qed.

Lemma ciu_jTy_rel_sym
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) (R : tm -> tm -> Prop) :
  (forall v1 v2, R v1 v2 -> R v2 v1) ->
  ciu_jTy_rel Σenv Γ t u A R ->
  ciu_jTy_rel Σenv Γ u t A R.
Proof.
  intros Hsym [Htu Hut].
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Hut Δ σ v Hσ Hvσ Hterm) as [v' [Hterm' HR]].
    exists v'. split; [exact Hterm'|exact (Hsym _ _ HR)].
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Htu Δ σ v Hσ Hvσ Hterm) as [v' [Hterm' HR]].
    exists v'. split; [exact Hterm'|exact (Hsym _ _ HR)].
Qed.

Lemma ciu_jTy_rel_trans
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u w A : tm)
    (Rtu Ruw Rtw : tm -> tm -> Prop) :
  (forall v1 v2 v3, Rtu v1 v2 -> Ruw v2 v3 -> Rtw v1 v3) ->
  ciu_jTy_rel Σenv Γ t u A Rtu ->
  ciu_jTy_rel Σenv Γ u w A Ruw ->
  ciu_jTy_rel Σenv Γ t w A Rtw.
Proof.
  intros Hcomp [Htu Hut] [Huw Hwu].
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Htu Δ σ v Hσ Hvσ Hterm) as [v2 [Hterm2 HR12]].
    destruct (Huw Δ σ v2 Hσ Hvσ Hterm2) as [v3 [Hterm3 HR23]].
    exists v3. split; [exact Hterm3|exact (Hcomp _ _ _ HR12 HR23)].
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Hwu Δ σ v Hσ Hvσ Hterm) as [v2 [Hterm2 HR23]].
    destruct (Hut Δ σ v2 Hσ Hvσ Hterm2) as [v3 [Hterm3 HR12]].
    exists v3. split; [exact Hterm3|].
    exact (Hcomp _ _ _ HR12 HR23).
Qed.

Lemma ciu_jTy_rel_of_ciu_jTy
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) :
  ciu_jTy Σenv Γ t u A ->
  ciu_jTy_rel Σenv Γ t u A eq.
Proof.
  intros [Htu Hut].
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    exists v. split.
    + apply Htu with (Δ := Δ) (σ := σ); assumption.
    + reflexivity.
  - intros Δ σ v Hσ Hvσ Hterm.
    exists v. split.
    + apply Hut with (Δ := Δ) (σ := σ); assumption.
    + reflexivity.
Qed.

Lemma ciu_jTy_of_ciu_jTy_rel_eq
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) :
  ciu_jTy_rel Σenv Γ t u A eq ->
  ciu_jTy Σenv Γ t u A.
Proof.
  intros [Htu Hut].
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Htu Δ σ v Hσ Hvσ Hterm) as [v' [Hterm' Heq]].
    subst v'. exact Hterm'.
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Hut Δ σ v Hσ Hvσ Hterm) as [v' [Hterm' Heq]].
    subst v'. exact Hterm'.
Qed.

Lemma ciu_jTy_iff_rel_eq
    (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) :
  ciu_jTy Σenv Γ t u A <-> ciu_jTy_rel Σenv Γ t u A eq.
Proof.
  split.
  - apply ciu_jTy_rel_of_ciu_jTy.
  - apply ciu_jTy_of_ciu_jTy_rel_eq.
Qed.

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
  intros ->. apply ciu_jTy_refl.
Qed.
