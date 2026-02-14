From Stdlib Require Import List Arith Utf8.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import SequentDrivingRules.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module SP := StrictPos.
Module SDR := SequentDrivingRules.

(** Observation sequents for inductives (starting with Nat)

    This module explains the "Nat-specific" descent that showed up in the
    supercompiler: it is not a typing-level driving rule, but an *observation*
    rule.

    In our call-by-name semantics, any constructor [tRoll] is a value regardless
    of its arguments. If we observe naturals extensionally as numerals, then to
    observe [S n] we must recursively observe the thunk stored in the [Succ]
    constructor.

    This is fully abstract as an *observation principle* (it depends only on how
    the observer interrogates a value), and it should not be confused with a
    conversion/rewriting rule for [jTy].
*)

Inductive nat_obs (t : tm) : nat -> Prop :=
| nat_obs_zero :
    steps t (tRoll 0 0 []) ->
    nat_obs t 0
| nat_obs_succ t' n :
    steps t (tRoll 0 1 [t']) ->
    nat_obs t' n ->
    nat_obs t (S n).

(** A small sequent-style judgement packaging Nat observations in context.

    This is deliberately minimal for now: we only need it to make the
    correspondence story precise ("descending under Succ" is a proof-search move
    for Nat observations).
*)
Inductive obs_tree : Type :=
| obsCtor (c : nat) (recs : list obs_tree).

(** Generic extensional observation for (non-indexed) inductives.

    This observes an inductive value by its top-level constructor tag and then
    recursively observing its recursive fields.

    For our current term calculus/typing, inductives are used at empty argument
    lists ([tInd I []]) and recursive fields have type [tInd I []].
*)
Inductive ind_obs (Σenv : Ty.env) (I : nat) (t : tm) : obs_tree -> Prop :=
| ind_obs_ctor ΣI ctor c args params recs orec :
    SP.lookup_ind Σenv I = Some ΣI ->
    SP.lookup_ctor ΣI c = Some ctor ->
    Ty.split_at (SP.ctor_param_arity ctor) args = (params, recs) ->
    length recs = SP.ctor_rec_arity ctor ->
    steps t (tRoll I c args) ->
    Forall2 (ind_obs Σenv I) recs orec ->
    ind_obs Σenv I t (obsCtor c orec).

Inductive judgement : Type :=
| jNatObs (Γ : Ty.ctx) (t : tm) (n : nat)
| jIndObs (Γ : Ty.ctx) (I : nat) (t : tm) (o : obs_tree).

Inductive rule (Σenv : Ty.env) : judgement -> list judgement -> Prop :=
(** Asynchronous driving steps for observations.

    These allow proof search for observations to simplify the observed term
    before applying the constructor/branch rules.
*)
| r_obs_drive_nat Γ t n t' :
    SDR.drive_cbn_onceR t t' ->
    t' <> t ->
    rule Σenv (jNatObs Γ t n) [jNatObs Γ t' n]
| r_obs_drive_ind Γ I t o t' :
    SDR.drive_cbn_onceR t t' ->
    t' <> t ->
    rule Σenv (jIndObs Γ I t o) [jIndObs Γ I t' o]

| r_obs_commute_case_case_nat Γ t n t' :
    t' = SDR.CC.commute_case_case_once_typed Σenv t ->
    t' <> t ->
    rule Σenv (jNatObs Γ t n) [jNatObs Γ t' n]
| r_obs_commute_case_case_ind Γ I t o t' :
    t' = SDR.CC.commute_case_case_once_typed Σenv t ->
    t' <> t ->
    rule Σenv (jIndObs Γ I t o) [jIndObs Γ I t' o]

| r_obs_commute_case_case_scrut_nat Γ t n t' :
    t' = SDR.commute_case_case_in_scrut Σenv t ->
    t' <> t ->
    rule Σenv (jNatObs Γ t n) [jNatObs Γ t' n]
| r_obs_commute_case_case_scrut_ind Γ I t o t' :
    t' = SDR.commute_case_case_in_scrut Σenv t ->
    t' <> t ->
    rule Σenv (jIndObs Γ I t o) [jIndObs Γ I t' o]

| r_obs_propagate_motive_nat Γ t n t' :
    t' = SDR.CC.propagate_motive_once t ->
    t' <> t ->
    rule Σenv (jNatObs Γ t n) [jNatObs Γ t' n]
| r_obs_propagate_motive_ind Γ I t o t' :
    t' = SDR.CC.propagate_motive_once t ->
    t' <> t ->
    rule Σenv (jIndObs Γ I t o) [jIndObs Γ I t' o]

(** Constructor observation rules. *)
| r_nat_zero Γ t :
    steps t (tRoll 0 0 []) ->
    rule Σenv (jNatObs Γ t 0) []
| r_nat_succ Γ t n t' :
    steps t (tRoll 0 1 [t']) ->
    rule Σenv (jNatObs Γ t (S n)) [jNatObs Γ t' n]

| r_ind_ctor Γ I t ΣI ctor c args params recs orec :
    SP.lookup_ind Σenv I = Some ΣI ->
    SP.lookup_ctor ΣI c = Some ctor ->
    Ty.split_at (SP.ctor_param_arity ctor) args = (params, recs) ->
    length recs = SP.ctor_rec_arity ctor ->
    length orec = length recs ->
    steps t (tRoll I c args) ->
    rule Σenv (jIndObs Γ I t (obsCtor c orec))
      (map (fun '(r, o) => jIndObs Γ I r o) (combine recs orec)).

Lemma nat_obs_steps_congr (t u : tm) (n : nat) :
  steps t u -> nat_obs t n <-> nat_obs u n.
Proof.
  intro Htu.
  split.
  - intro Hobs.
    inversion Hobs as [Hzero|tpred n' Hstep Hrec]; subst.
    + apply nat_obs_zero.
      eapply steps_to_value_unique; eauto.
      apply v_roll.
    + apply nat_obs_succ with tpred.
      * eapply steps_to_value_unique; eauto.
        apply v_roll.
      * exact Hrec.
  - intro Hobs.
    inversion Hobs as [Hzero|tpred n' Hstep Hrec]; subst.
    + apply nat_obs_zero.
      eapply steps_trans; eauto.
    + apply nat_obs_succ with tpred.
      * eapply steps_trans; eauto.
      * exact Hrec.
Qed.

Lemma ind_obs_steps_congr (Σenv : Ty.env) (I : nat) (t u : tm) (o : obs_tree) :
  steps t u -> ind_obs Σenv I t o <-> ind_obs Σenv I u o.
Proof.
  intro Htu.
  split.
  - intro Hobs.
    inversion Hobs; subst.
    econstructor; eauto.
    eapply steps_to_value_unique; eauto.
    apply v_roll.
  - intro Hobs.
    inversion Hobs; subst.
    econstructor; eauto.
    eapply steps_trans; eauto.
Qed.

Lemma obs_drive_cbn_preserves_nat (Γ : Ty.ctx) (t t' : tm) (n : nat) :
  SDR.drive_cbn_onceR t t' -> nat_obs t n <-> nat_obs t' n.
Proof.
  intro H.
  apply nat_obs_steps_congr.
  apply SDR.drive_cbn_onceR_steps.
  exact H.
Qed.

Lemma obs_drive_cbn_preserves_ind
    (Σenv : Ty.env) (Γ : Ty.ctx) (I : nat) (t t' : tm) (o : obs_tree) :
  SDR.drive_cbn_onceR t t' -> ind_obs Σenv I t o <-> ind_obs Σenv I t' o.
Proof.
  intro H.
  apply ind_obs_steps_congr.
  apply SDR.drive_cbn_onceR_steps.
  exact H.
Qed.
