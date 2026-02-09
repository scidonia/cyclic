From Stdlib Require Import List.
From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Judgement Require Import Typing.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.

(** A more extensional observation for natural numbers.

    In our CBN semantics, any constructor [tRoll] is a value, even if its
    arguments are not values. This makes the existing CIU (which observes a
    *syntactic* value) too intensional for transformations like deforestation.

    Here we observe naturals as numerals: to observe [S n] we must recursively
    observe the thunk stored in the [succ] constructor.
*)

Inductive terminates_to_nat (t : tm) : nat -> Prop :=
| tt_nat_zero :
    steps t (tRoll 0 0 []) ->
    terminates_to_nat t 0
| tt_nat_succ t' n :
    steps t (tRoll 0 1 [t']) ->
    terminates_to_nat t' n ->
    terminates_to_nat t (S n).

Lemma terminates_to_nat_zero_inv (t : tm) :
  terminates_to_nat t 0 -> steps t (tRoll 0 0 []).
Proof.
  intro H.
  inversion H; subst; eauto.
Qed.

Lemma terminates_to_nat_succ_inv (t : tm) (n : nat) :
  terminates_to_nat t (S n) -> exists t', steps t (tRoll 0 1 [t']) /\ terminates_to_nat t' n.
Proof.
  intro H.
  inversion H; subst.
  exists t'. eauto.
Qed.

(** A binary relation on (not-necessarily-normal) Nat terms, observed as numerals. *)
Definition nat_obs_rel (t u : tm) : Prop :=
  forall n : nat, terminates_to_nat t n <-> terminates_to_nat u n.

Lemma nat_obs_rel_refl (t : tm) : nat_obs_rel t t.
Proof.
  intros n. tauto.
Qed.

Lemma nat_obs_rel_sym (t u : tm) : nat_obs_rel t u -> nat_obs_rel u t.
Proof.
  intros H n.
  specialize (H n).
  tauto.
Qed.

Lemma nat_obs_rel_trans (t u w : tm) :
  nat_obs_rel t u -> nat_obs_rel u w -> nat_obs_rel t w.
Proof.
  intros Htu Huw n.
  specialize (Htu n).
  specialize (Huw n).
  tauto.
Qed.

(** Typed CIU for terms of type [Nat], using [terminates_to_nat] as observation. *)
Definition ciu_jNatObs (Σenv : Ty.env) (Γ : Ty.ctx) (t u : tm) : Prop :=
  forall (Δ : Ty.ctx) (σ : list tm),
    Ty.has_subst Σenv Δ σ Γ ->
    Forall value σ ->
    forall n : nat,
      terminates_to_nat (Ty.subst_list σ t) n <-> terminates_to_nat (Ty.subst_list σ u) n.

Lemma ciu_jNatObs_refl (Σenv : Ty.env) (Γ : Ty.ctx) (t : tm) :
  ciu_jNatObs Σenv Γ t t.
Proof.
  intros Δ σ _ _ n. tauto.
Qed.

Lemma ciu_jNatObs_sym (Σenv : Ty.env) (Γ : Ty.ctx) (t u : tm) :
  ciu_jNatObs Σenv Γ t u -> ciu_jNatObs Σenv Γ u t.
Proof.
  intros H Δ σ Hσ Hv n.
  specialize (H Δ σ Hσ Hv n).
  tauto.
Qed.

Lemma ciu_jNatObs_trans (Σenv : Ty.env) (Γ : Ty.ctx) (t u w : tm) :
  ciu_jNatObs Σenv Γ t u ->
  ciu_jNatObs Σenv Γ u w ->
  ciu_jNatObs Σenv Γ t w.
Proof.
  intros Htu Huw Δ σ Hσ Hv n.
  specialize (Htu Δ σ Hσ Hv n).
  specialize (Huw Δ σ Hσ Hv n).
  tauto.
Qed.
