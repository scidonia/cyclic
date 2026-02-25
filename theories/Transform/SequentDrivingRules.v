From Stdlib Require Import List Bool Arith Utf8 Relations Relation_Operators.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Transform Require Import CaseCase Supercompile.
From Cyclic.Progress Require Import PatternUnification.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module CC := CaseCase.
Module SC := Supercompile.
Module PU := PatternUnification.
Module SP := StrictPos.

Definition tm_eqb : tm -> tm -> bool := PU.tm_eqb.

(** Sequent-level driving rules (first cut)

    This file makes the "driving" component of supercompilation explicit as a
    sequent-style rule relation on configurations.

    A configuration is a cyclic typing judgement [C.jTy Γ t A].

    Each driving step is presented as a rule that rewrites the term position of
    the goal, leaving the context and type untouched.

    These rules are intended to be the asynchronous/invertible moves in a
    focused cyclic sequent proof search presentation.
*)

Definition config : Type := C.judgement.

Definition commute_case_case_in_scrut (Σenv : Ty.env) (t : tm) : tm :=
  match t with
  | tCase ind scrut Cmot brs =>
      let scrut' := CC.commute_case_case_once_typed Σenv scrut in
      if tm_eqb scrut scrut' then t else tCase ind scrut' Cmot brs
  | _ => t
  end.

Definition fresh_args (n : nat) : list tm :=
  rev (map tVar (seq 0 n)).

Definition subst_one (k : nat) (u : tm) : var -> tm :=
  fun x => if Nat.eqb x k then u else tVar x.

Definition extend_ctx (tys : list tm) (Γ : Ty.ctx) : Ty.ctx :=
  rev tys ++ Γ.

(** Case-splitting / information propagation (neutral scrutinee).

    For now, we re-use the supercompiler's implementation so that the sequent
    rule matches the operational split exactly.
*)
Definition split_case_var_cfgs := SC.split_case_var.

(** One-step CBN driving, presented relationally.

    This is the graph of the function [Supercompile.drive_cbn_once], but written
    as explicit rule cases.
*)
Inductive drive_cbn_onceR : tm -> tm -> Prop :=
| dc_var x :
    drive_cbn_onceR (tVar x) (tVar x)
| dc_sort i :
    drive_cbn_onceR (tSort i) (tSort i)
| dc_pi A B :
    drive_cbn_onceR (tPi A B) (tPi A B)
| dc_lam A body :
    drive_cbn_onceR (tLam A body) (tLam A body)
| dc_ind ind args :
    drive_cbn_onceR (tInd ind args) (tInd ind args)
| dc_roll ind c args :
    drive_cbn_onceR (tRoll ind c args) (tRoll ind c args)

| dc_fix A body :
    drive_cbn_onceR (tFix A body) (subst0 (tFix A body) body)

| dc_app_beta t1 t2 A body t1' :
    drive_cbn_onceR t1 t1' ->
    t1' = tLam A body ->
    drive_cbn_onceR (tApp t1 t2) (subst0 t2 body)

| dc_app_cong t1 t2 t1' :
    drive_cbn_onceR t1 t1' ->
    (forall A body, t1' <> tLam A body) ->
    drive_cbn_onceR (tApp t1 t2) (tApp t1' t2)

| dc_case_iota ind ind' c args scrut Cmot brs br :
    scrut = tRoll ind' c args ->
    ind = ind' ->
    branch brs c = Some br ->
    drive_cbn_onceR (tCase ind scrut Cmot brs) (Cbn.apps br args)

| dc_case_roll_ind_mismatch ind ind' c args scrut Cmot brs :
    scrut = tRoll ind' c args ->
    ind <> ind' ->
    drive_cbn_onceR (tCase ind scrut Cmot brs) (tCase ind scrut Cmot brs)

| dc_case_roll_no_branch ind ind' c args scrut Cmot brs :
    scrut = tRoll ind' c args ->
    ind = ind' ->
    branch brs c = None ->
    drive_cbn_onceR (tCase ind scrut Cmot brs) (tCase ind scrut Cmot brs)

| dc_case_scrut_step ind scrut Cmot brs scrut' :
    (forall ind' c args, scrut <> tRoll ind' c args) ->
    drive_cbn_onceR scrut scrut' ->
    scrut' <> scrut ->
    drive_cbn_onceR (tCase ind scrut Cmot brs) (tCase ind scrut' Cmot brs)

| dc_case_scrut_stuck ind scrut Cmot brs scrut' :
    (forall ind' c args, scrut <> tRoll ind' c args) ->
    drive_cbn_onceR scrut scrut' ->
    scrut' = scrut ->
    drive_cbn_onceR (tCase ind scrut Cmot brs) (tCase ind scrut Cmot brs).

(** Driving moves as explicit sequent rules on configurations.

    Each rule produces exactly one successor configuration.
    (Case splitting and generalisation will add multi-premise rules later.)
*)
Inductive drive_rule (Σenv : Ty.env) : config -> list config -> Prop :=
| dr_cbn_once Γ t A u :
    drive_cbn_onceR t u ->
    u <> t ->
    drive_rule Σenv (C.jTy Γ t A) [C.jTy Γ u A]

| dr_commute_case_case Γ t A u :
    u = CC.commute_case_case_once_typed Σenv t ->
    u <> t ->
    drive_rule Σenv (C.jTy Γ t A) [C.jTy Γ u A]

| dr_commute_case_case_scrut Γ t A u :
    u = commute_case_case_in_scrut Σenv t ->
    u <> t ->
    drive_rule Σenv (C.jTy Γ t A) [C.jTy Γ u A]

| dr_propagate_motive Γ t A u :
    u = CC.propagate_motive_once t ->
    u <> t ->
    drive_rule Σenv (C.jTy Γ t A) [C.jTy Γ u A]

(* Nat observation is handled by a separate observation judgement;
   see [Transform/SequentObservationRules.v]. *)

| dr_split_case_var Γ ind x Cmot brs A succs :
    succs = split_case_var_cfgs Σenv Γ ind x Cmot brs A ->
    succs <> [] ->
    drive_rule Σenv (C.jTy Γ (tCase ind (tVar x) Cmot brs) A) succs.

Lemma drive_cbn_onceR_steps (t u : tm) :
  drive_cbn_onceR t u -> steps t u.
Proof.
  intro H.
  induction H.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - (* fix *)
    apply steps_step.
    constructor.
  - (* app beta *)
    subst.
    eapply steps_trans.
    + apply steps_app1. exact IHdrive_cbn_onceR.
    + apply steps_step. constructor.
  - (* app cong *)
    apply steps_app1.
    exact IHdrive_cbn_onceR.
  - (* case iota *)
    subst scrut.
    subst ind.
    apply steps_step.
    econstructor.
    exact H1.
  - (* case roll ind mismatch *)
    apply rt_refl.
  - (* case roll no branch *)
    apply rt_refl.
  - (* case scrut step *)
    apply steps_case_scrut_congr.
    exact IHdrive_cbn_onceR.
  - (* case scrut stuck *)
    subst.
    apply rt_refl.
Qed.
