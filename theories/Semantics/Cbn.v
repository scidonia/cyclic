From Stdlib Require Import List Utf8 Relations Relation_Operators.
From Stdlib Require Import FunctionalExtensionality.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

(* Call-by-name (weak-head) operational semantics for raw terms.

   We reduce only in:
   - function position of application
   - scrutinee position of case
   - the head of a fix

   Arguments are never evaluated before substitution.
*)

Fixpoint apps (t : tm) (us : list tm) : tm :=
  match us with
  | [] => t
  | u :: us => apps (tApp t u) us
  end.

Inductive step : tm -> tm -> Prop :=
| step_beta A t u :
    step (tApp (tLam A t) u) (subst0 u t)
| step_app1 t t' u :
    step t t' ->
    step (tApp t u) (tApp t' u)
| step_fix A t :
    step (tFix A t) (subst0 (tFix A t) t)
| step_case_scrut I scrut scrut' C brs :
    step scrut scrut' ->
    step (tCase I scrut C brs) (tCase I scrut' C brs)
 | step_case_roll I c args C brs br :
     branch brs c = Some br ->
     step (tCase I (tRoll I c args) C brs) (apps br args).

Inductive clos_refl_trans_2 {A : Type} (R : relation A) (x : A) : A -> Prop :=
  | rt2_step : forall y, R x y -> clos_refl_trans_2 R x y
  | rt2_refl : clos_refl_trans_2 R x x
  | rt2_trans : forall y z,
      clos_refl_trans_2 R x y -> clos_refl_trans_2 R y z -> clos_refl_trans_2 R x z.

Lemma clos_refl_trans_2_ind_old (A : Type) (R : relation A) (x : A) (P : A -> Prop) :
  P x ->
  (forall y z, clos_refl_trans_2 R x y -> R y z -> P y -> P z) ->
  forall y, clos_refl_trans_2 R x y -> P y.
Proof.
  intros Hbase Hstep y Hclos.
  refine ((fix go a b (H : clos_refl_trans_2 R a b) {struct H} :
    clos_refl_trans_2 R x a -> P a -> P b :=
    _) x y Hclos (@rt2_refl A R x) Hbase).
  intros Hxa Pa. destruct H as [b' Hstep_ab | | m n H1 H2].
  - exact (Hstep a b' Hxa Hstep_ab Pa).
  - exact Pa.
  - pose (Pm := go a m H1 Hxa Pa).
    exact (go m n H2 (@rt2_trans A R x a m Hxa H1) Pm).
Defined.

Lemma clos_refl_trans_2_to_builtin {A R x y} :
  clos_refl_trans_2 R x y -> clos_refl_trans A R x y.
Proof.
  intro H.
  refine ((fix go x' y' (Hst : clos_refl_trans_2 R x' y') {struct Hst} :
    clos_refl_trans A R x' y' :=
    match Hst with
    | @rt2_step _ _ _ y'' Hs => @rt_step A R x' y'' Hs
    | @rt2_refl _ _ _ => @rt_refl A R x'
    | @rt2_trans _ _ _ y'' z'' H1 H2 =>
        @rt_trans A R x' y'' z'' (go x' y'' H1) (go y'' z'' H2)
    end) x y H).
Qed.

Definition steps : tm -> tm -> Prop :=
  clos_refl_trans_2 step.

Inductive value : tm -> Prop :=
| v_lam A t : value (tLam A t)
| v_roll I c args : value (tRoll I c args).

(* Neutrals are stuck at the head (no CBN reduction possible). *)
Inductive neutral : tm -> Prop :=
| ne_var x : neutral (tVar x)
| ne_app t u : neutral t -> neutral (tApp t u)
| ne_case I t C brs : neutral t -> neutral (tCase I t C brs).

(* Weak-head normal forms: values or neutrals. *)
Inductive whnf : tm -> Prop :=
| whnf_val v : value v -> whnf v
| whnf_ne t : neutral t -> whnf t.

Definition eval_whnf (t w : tm) : Prop :=
  steps t w ∧ whnf w.

Notation "t ⇓wh w" := (eval_whnf t w) (at level 70).

Definition terminates_to (t v : tm) : Prop :=
  steps t v ∧ value v.

Definition terminates (t : tm) : Prop :=
  ∃ v, terminates_to t v.

CoInductive diverges (t : tm) : Prop :=
| diverges_step t' : step t t' -> diverges t' -> diverges t.

Lemma value_no_step (v v' : tm) :
  value v -> step v v' -> False.
Proof.
  intros Hv Hstep.
  inversion Hv; subst; inversion Hstep.
Qed.

Lemma neutral_no_step (t t' : tm) :
  neutral t -> step t t' -> False.
Proof.
  intro Hn.
  revert t'.
  induction Hn as [x|t u Ht IH|I t C brs Ht IH]; intro t'; intro Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + inversion Ht.
    + eapply IH; eauto.
  - inversion Hstep; subst.
    + eapply IH; eauto.
    + inversion Ht.
Qed.

Lemma whnf_no_step (t t' : tm) :
  whnf t -> step t t' -> False.
Proof.
  intros Hwh Hstep.
  inversion Hwh; subst.
  - exact (value_no_step _ _ H Hstep).
  - exact (neutral_no_step _ _ H Hstep).
Qed.

Lemma step_deterministic (t t1 t2 : tm) :
  step t t1 -> step t t2 -> t1 = t2.
Proof.
  intro H1.
  revert t2.
  induction H1 as
    [A body u
    | t t' u Htt' IH
    | A body
    | I scrut scrut' C brs Hscrut IH
    | I c args C brs br Hbr];
    intro t2; intro H2.
  - (* beta *)
    inversion H2; subst; try reflexivity; try discriminate.
    (* cannot also step in function position: lambdas do not step *)
    exfalso.
    match goal with
    | H : step (tLam _ _) _ |- _ => eapply value_no_step; [apply v_lam|exact H]
    end.
  - (* app1 *)
    inversion H2; subst; try discriminate.
    + (* beta: would require t = tLam, impossible since it steps *)
      exfalso.
      match goal with
      | H : step (tLam _ _) _ |- _ => eapply value_no_step; [apply v_lam|exact H]
      end.
    + (* app1 *)
      f_equal. eapply IH; eauto.
  - (* fix *)
    inversion H2; subst; reflexivity.
  - (* case scrut *)
    inversion H2; subst; try discriminate.
    + (* case scrut *)
      f_equal. eapply IH; eauto.
    + (* case roll: scrutinee is a roll, but rolls do not step *)
      exfalso.
      eapply value_no_step.
      * apply v_roll.
      * exact Hscrut.
  - (* case roll *)
    inversion H2; subst; try discriminate.
    { (* case scrut cannot apply: roll doesn't step *)
      exfalso.
      match goal with
      | Hstep : step (tRoll _ _ _) _ |- _ =>
          eapply value_no_step; [apply v_roll|exact Hstep]
      end. }
    { (* both case roll *)
      assert (br0 = br) as -> by congruence.
      reflexivity. }
Qed.

(** Convenience lemmas for reasoning about `steps` (CBN evaluation). *)

Lemma steps_step (t u : tm) : step t u -> steps t u.
Proof.
  intro H.
  apply rt2_step.
  exact H.
Qed.

Lemma steps_trans (t u v : tm) : steps t u -> steps u v -> steps t v.
Proof.
  intros Htu Huv.
  eapply rt2_trans; eauto.
Qed.

Lemma steps_app1 (t t' u : tm) : steps t t' -> steps (tApp t u) (tApp t' u).
Proof.
  intro Hsteps.
  revert u.
  induction Hsteps; intro u.
  - (* rt2_step *)
    apply rt2_step.
    eapply step_app1; eauto.
  - (* rt2_refl *)
    apply rt2_refl.
  - (* rt2_trans *)
    eapply rt2_trans.
    + apply IHHsteps1.
    + apply IHHsteps2.
Qed.

Lemma steps_case_scrut_congr (I : nat) (scrut scrut' C : tm) (brs : list tm) :
  steps scrut scrut' -> steps (tCase I scrut C brs) (tCase I scrut' C brs).
Proof.
  intro Hsteps.
  revert C brs.
  induction Hsteps; intros C0 brs0.
  - (* rt2_step *)
    apply rt2_step.
    eapply step_case_scrut; eauto.
  - (* rt2_refl *)
    apply rt2_refl.
  - (* rt2_trans *)
    eapply rt2_trans.
    + apply IHHsteps1.
    + apply IHHsteps2.
Qed.

Lemma steps_apps_congr (t t' : tm) (us : list tm) :
  steps t t' -> steps (apps t us) (apps t' us).
Proof.
  revert t t'.
  induction us as [|u us IH]; intros t t' H.
  - cbn [apps]. exact H.
  - cbn [apps].
    apply IH.
    apply steps_app1.
    exact H.
Qed.

Lemma steps_case_to_apps
    (I : nat) (scrut C : tm) (brs : list tm)
    (c : nat) (args : list tm) (br : tm) :
  steps scrut (tRoll I c args) ->
  branch brs c = Some br ->
  steps (tCase I scrut C brs) (apps br args).
Proof.
  intros Hscrut Hbr.
  eapply steps_trans.
  - apply steps_case_scrut_congr. exact Hscrut.
  - apply steps_step.
    apply step_case_roll.
    exact Hbr.
Qed.

Lemma steps_decomp (t u : tm) :
  steps t u -> t = u \/ exists t1, step t t1 /\ steps t1 u.
Proof.
  intro H.
  induction H.
  - (* rt2_step *)
    right. exists y. split; [exact H|apply rt2_refl].
  - (* rt2_refl *)
    left. reflexivity.
  - (* rt2_trans *)
    destruct IHclos_refl_trans_2_1 as [->|[t1 [Hst Ht1u]]].
    + (* t = y *)
      destruct IHclos_refl_trans_2_2 as [->|[t1 [Hst Ht1u]]].
      * left. reflexivity.
      * right. exists t1. split; [exact Hst|exact Ht1u].
    + right. exists t1. split; [exact Hst|].
      eapply rt2_trans; eauto.
Qed.

Lemma steps_to_value_unique (t u v : tm) :
  steps t v -> value v -> steps t u -> steps u v.
Proof.
  intros Htv Hv Htu.
  revert v Htv Hv.
  induction Htu.
  - (* rt2_step *)
    intros v Htv Hv.
    destruct (steps_decomp _ _ Htv) as [->|[t1 [Hst Ht1v]]].
    + exfalso. eapply value_no_step; eauto.
    + assert (y = t1) as -> by (eapply step_deterministic; eauto).
      exact Ht1v.
  - (* rt2_refl *)
    intros v Htv _. exact Htv.
  - (* rt2_trans *)
    intros v Htv Hv.
    pose proof (IHHtu1 v Htv Hv) as Hmv.
    apply IHHtu2; [exact Hmv|exact Hv].
Qed.

Lemma terminates_to_steps_prefix (t u v : tm) :
  steps t u -> terminates_to t v -> terminates_to u v.
Proof.
  intros Htu [Htv Hv].
  split.
  - eapply steps_to_value_unique; eauto.
  - exact Hv.
Qed.

Lemma branch_subst (σ : var -> tm) (brs : list tm) (c : nat) :
  branch (map (fun t => t.[σ]) brs) c = option_map (fun t => t.[σ]) (branch brs c).
Proof.
  unfold branch.
  rewrite nth_error_map.
  reflexivity.
Qed.

Lemma subst0_subst (σ : var -> tm) (u : tm) (t : tm) :
  (subst0 u t).[σ] = subst0 u.[σ] t.[up σ].
Proof.
  unfold subst0.
  asimpl.
  apply (f_equal (fun θ => t.[θ])).
  extensionality x.
  destruct x as [|x].
  - asimpl. reflexivity.
  - cbn.
    unfold scomp.
    cbn.
    unfold up.
    unfold Autosubst_Classes.up.
    cbn.
    asimpl.
    reflexivity.
Qed.

Lemma list_subst_as_map (σ : var -> tm) (ts : list tm) :
  ts..[σ] = map (fun t => t.[σ]) ts.
Proof.
  induction ts as [|t ts IH]; cbn; [reflexivity|].
  f_equal; auto.
Qed.

Lemma apps_subst (σ : var -> tm) (t : tm) (us : list tm) :
  (apps t us).[σ] = apps (t.[σ]) (map (fun u => u.[σ]) us).
Proof.
  revert t.
  induction us as [|u us IH]; intro t; cbn [apps].
  - reflexivity.
  - (* apply IH to the accumulator (tApp t u) *)
    specialize (IH (tApp t u)).
    rewrite IH.
    asimpl.
    reflexivity.
Qed.

Lemma step_subst (σ : var -> tm) (t u : tm) :
  step t u -> step t.[σ] u.[σ].
Proof.
  intro Hstep.
  induction Hstep.
  - (* beta *)
    asimpl.
    rewrite subst0_subst.
    apply step_beta.
  - (* app1 *)
    asimpl.
    apply step_app1.
    exact IHHstep.
  - (* fix *)
    asimpl.
    rewrite subst0_subst.
    apply step_fix.
  - (* case scrut *)
    asimpl.
    apply step_case_scrut.
    exact IHHstep.
  - (* case roll *)
    asimpl.
    rewrite (list_subst_as_map σ args).
    rewrite (list_subst_as_map σ brs).
    rewrite apps_subst.
    apply step_case_roll.
    unfold branch.
    rewrite nth_error_map.
    unfold branch in H.
    rewrite H.
    reflexivity.
Qed.

Lemma steps_subst (σ : var -> tm) (t u : tm) :
  steps t u -> steps t.[σ] u.[σ].
Proof.
  intro H.
  induction H.
  - apply rt2_step.
    now apply step_subst.
  - apply rt2_refl.
  - eapply rt2_trans; eauto.
Qed.

(** Decomposition: if [tCase I scrut C brs] steps to a value [v],
    the scrutinee must step to a [tRoll], the branch must fire,
    and the branch+args must step to [v]. *)
Lemma steps_tCase_decompose (I : nat) (scrut C : tm) (brs : list tm) (v : tm) :
  value v -> steps (tCase I scrut C brs) v ->
  exists c args br,
    steps scrut (tRoll I c args) /\
    branch brs c = Some br /\
    steps (apps br args) v.
Proof.
  intros Hval Hsteps.
  refine (clos_refl_trans_2_ind_old tm step (tCase I scrut C brs)
    (fun w => value w -> exists c args br,
      steps scrut (tRoll I c args) /\
      branch brs c = Some br /\
      steps (apps br args) w) _ _ v Hsteps Hval).
  - (* base case: P (tCase ...) = value (tCase ...) -> ... *)
    intros Hv. inversion Hv.
  - (* step case: P y -> step y z -> P z *)
    intros y z Hclos Hstep H_IH Hvz.
    inversion Hstep; subst; clear Hstep.
    + (* step_case_scrut *)
      refine (fun Hvz' => match Hvz' with end).
    + (* step_case_roll *)
      refine (fun Hvz' => _). inversion Hvz' || 
        (exists c, args, br; split; [apply rt2_refl|split; [exact H|apply rt2_refl]]).
Qed.

(** Corollary for [terminates_to]. *)
Lemma terminates_to_tCase_decompose (I : nat) (scrut C : tm) (brs : list tm) (v : tm) :
  terminates_to (tCase I scrut C brs) v ->
  exists c args br,
    terminates_to scrut (tRoll I c args) /\
    branch brs c = Some br /\
    terminates_to (apps br args) v.
Proof.
  intros [Hsteps Hval].
  apply steps_tCase_decompose in Hsteps; [|exact Hval].
  destruct Hsteps as [c [args [br [Hscrut [Hb Hbranch]]]]].
  exists c, args, br. split; [split|split].
  - exact Hscrut.
  - apply v_roll.
  - exact Hb.
  - exact Hbranch.
  - exact Hval.
Qed.

