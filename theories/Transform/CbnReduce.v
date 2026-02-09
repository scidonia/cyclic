From Stdlib Require Import List.
Import ListNotations.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Equiv Require Import CIUJudgement.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import BetaReduce.
From Cyclic.Progress Require Import PatternUnification.

Import Term.Syntax.

Module Ty := Typing.Typing.

(** One-step fix unfolding at the head. *)
Definition fix_unfold_once (t : tm) : tm :=
  match t with
  | tFix A body => subst0 (tFix A body) body
  | _ => t
  end.

(** One-step iota reduction for case-of-constructor at the head. *)
Definition iota_reduce_once (t : tm) : tm :=
  match t with
  | tCase ind (tRoll ind' c args) C brs =>
      if Nat.eqb ind ind' then
        match branch brs c with
        | Some br => apps br args
        | None => t
        end
      else t
  | _ => t
  end.

Lemma step_fix_unfold_once (A body : tm) :
  step (tFix A body) (fix_unfold_once (tFix A body)).
Proof.
  cbn [fix_unfold_once].
  apply step_fix.
Qed.

Lemma step_iota_reduce_once (ind ind' c : nat) (args : list tm) (C : tm) (brs : list tm) (br : tm) :
  Nat.eqb ind ind' = true ->
  branch brs c = Some br ->
  step (tCase ind (tRoll ind' c args) C brs) (iota_reduce_once (tCase ind (tRoll ind' c args) C brs)).
Proof.
  intros Heq Hbr.
  apply Nat.eqb_eq in Heq.
  subst ind'.
  cbn [iota_reduce_once].
  rewrite Nat.eqb_refl.
  rewrite Hbr.
  apply step_case_roll.
  exact Hbr.
Qed.

(** A tiny fuel-based evaluator step: prefer β, then iota, then fix. *)
Definition cbn_eval_once (t : tm) : tm :=
  let t1 :=
    match t with
    | tApp (tLam A body) u => subst0 u body
    | _ => t
    end
  in
  if Term.Syntax.tm_eq_dec t t1 then
    let t2 := iota_reduce_once t in
    if Term.Syntax.tm_eq_dec t t2 then fix_unfold_once t else t2
  else t1.

Fixpoint cbn_eval_fuel (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S n =>
      let t' := cbn_eval_once t in
      if Term.Syntax.tm_eq_dec t t' then t else cbn_eval_fuel n t'
  end.

(** For closed terms (empty context), any single CBN step is CIU-preserving. *)
Lemma ciu_jTy_step_closed (Σenv : Ty.env) (t u A : tm) :
  step t u ->
  CIUJudgement.ciu_jTy Σenv [] t u A.
Proof.
  intro Hstep.
  unfold CIUJudgement.ciu_jTy.
  split.
  - intros Δ σ v Hσ _Hvσ Hterm.
    inversion Hσ; subst.
    cbn [Ty.subst_list Typing.Typing.subst_list Ty.subst_sub Typing.Typing.subst_sub] in *.
    (* Use termination equivalence across a single step. *)
    pose proof (BetaReduce.terminates_to_beta_step t u v Hstep) as Hiff.
    apply (proj1 Hiff).
    exact Hterm.
  - intros Δ σ v Hσ _Hvσ Hterm.
    inversion Hσ; subst.
    cbn [Ty.subst_list Typing.Typing.subst_list Ty.subst_sub Typing.Typing.subst_sub] in *.
    pose proof (BetaReduce.terminates_to_beta_step t u v Hstep) as Hiff.
    apply (proj2 Hiff).
    exact Hterm.
Qed.
