From Stdlib Require Import Utf8 List FunctionalExtensionality.
From Autosubst Require Import Autosubst.
From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.

Import Term.Syntax.
Import ListNotations.
Set Default Proof Using "Type".

Definition ciu (t u : tm) : Prop :=
  (forall (σ : var -> tm) (v : tm), terminates_to (t.[σ]) v -> terminates_to (u.[σ]) v)
  /\
  (forall (σ : var -> tm) (v : tm), terminates_to (u.[σ]) v -> terminates_to (t.[σ]) v).

Lemma ciu_refl (t : tm) : ciu t t.
Proof. split; intros σ v Hv; exact Hv. Qed.
Lemma ciu_sym (t u : tm) : ciu t u -> ciu u t.
Proof. intro H. destruct H as [Htu Hut]. split; assumption. Qed.
Lemma ciu_trans (t u w : tm) : ciu t u -> ciu u w -> ciu t w.
Proof.
  intros Htu Huw. destruct Htu as [Htu Hut]. destruct Huw as [Huw Hwu].
  split; [intros σ v Hv; apply Huw, Htu, Hv|intros σ v Hv; apply Hut, Hwu, Hv].
Qed.
Lemma ciu_of_eq (t u : tm) : t = u -> ciu t u.
Proof. intros ->. apply ciu_refl. Qed.

Lemma step_ciu (t u : tm) : step t u -> ciu t u.
Proof.
  intro Hstep. split.
  - intros σ v [Htv Hval]. pose proof (step_subst σ _ _ Hstep) as Hst.
    apply steps_step in Hst. apply (terminates_to_steps_prefix _ _ _ Hst). split; [exact Htv|exact Hval].
  - intros σ v [Huv Hval]. pose proof (step_subst σ _ _ Hstep) as Hst.
    apply steps_step in Hst. split; [eapply steps_trans; [exact Hst|exact Huv]|exact Hval].
Qed.

Lemma steps_ciu (t u : tm) : steps t u -> ciu t u.
Proof.
  intro Hsteps. induction Hsteps.
  - apply step_ciu. exact H. - apply ciu_refl. - eapply ciu_trans; eauto.
Qed.

Lemma ciu_beta (A arg body : tm) : ciu (tApp (tLam A body) arg) (subst0 arg body).
Proof. apply step_ciu. apply step_beta. Qed.
Lemma ciu_fix (A body : tm) : ciu (tFix A body) (subst0 (tFix A body) body).
Proof. apply step_ciu. apply step_fix. Qed.
Lemma ciu_case_iota (I c : nat) (args : list tm) (C : tm) (brs : list tm) (br : tm) :
  branch brs c = Some br -> ciu (tCase I (tRoll I c args) C brs) (apps br args).
Proof. intro Hbr. apply step_ciu. apply step_case_roll. exact Hbr. Qed.
Lemma ciu_case_scrut_congr (I : nat) (scrut scrut' C : tm) (brs : list tm) :
  steps scrut scrut' -> ciu (tCase I scrut C brs) (tCase I scrut' C brs).
Proof. intro Hsteps. apply steps_ciu. apply steps_case_scrut_congr. exact Hsteps. Qed.

Lemma shift_subst_eq (d : nat) (σ : var -> tm) (t : tm) :
  (shift d 0 t).[σ] = t.[shift_sub d 0 >>> σ].
Proof.
  unfold shift, rename.
  rewrite rename_subst.
  rewrite subst_comp.
  reflexivity.
Qed.

Lemma ciu_shift (d : nat) (t u : tm) : ciu t u -> ciu (shift d 0 t) (shift d 0 u).
Proof.
  intro Hciu. destruct Hciu as [Htu Hut]. split.
  - intros σ v Hterm.
    rewrite shift_subst_eq.
    apply Htu.
    rewrite <- shift_subst_eq.
    exact Hterm.
  - intros σ v Hterm.
    rewrite shift_subst_eq.
    apply Hut.
    rewrite <- shift_subst_eq.
    exact Hterm.
Qed.

Lemma terminates_to_tApp_decompose (t a v : tm) :
  terminates_to (tApp t a) v ->
  exists A body, terminates_to t (tLam A body) /\ terminates_to (subst0 a body) v.
Proof.
  intros [Hsteps Hval].
  assert (Hreach :
    (exists t', steps t t' /\ v = tApp t' a) \/
    (exists A body, steps t (tLam A body) /\ steps (subst0 a body) v)).
  { refine (clos_refl_trans_2_ind_old tm step (tApp t a)
      (fun w =>
        (exists t', steps t t' /\ w = tApp t' a) \/
        (exists A body, steps t (tLam A body) /\ steps (subst0 a body) w)) _ _ v Hsteps).
    - left. exists t. split; [apply rt2_refl|reflexivity].
    - intros y z _ Hstep H_IH.
      destruct H_IH as [[t' [Ht ->]]|[A [body [Ht Hbody]]]].
      + inversion Hstep; subst; clear Hstep.
        * right.
          match type of Ht with
          | steps _ (tLam ?A ?body) =>
              exists A, body; split; [exact Ht|apply rt2_refl]
          end.
        * left.
          match goal with
          | Hs : step t' ?t'' |- _ =>
              exists t''; split;
              [eapply rt2_trans; [exact Ht|apply rt2_step; exact Hs]
              |reflexivity]
          end.
      + right. exists A, body. split; [exact Ht|].
        eapply rt2_trans; [exact Hbody|].
        apply rt2_step. exact Hstep. }
  destruct Hreach as [[t' [_ Heq]]|[A [body [Ht Hbody]]]].
  - subst v. inversion Hval.
  - exists A, body. split.
    + split; [exact Ht|apply v_lam].
    + split; [exact Hbody|exact Hval].
Qed.

Lemma ciu_tApp (t u a : tm) : ciu t u -> ciu (tApp t a) (tApp u a).
Proof.
  intro Hciu. destruct Hciu as [Htu Hut]. split.
  - intros σ v Hterm.
    apply terminates_to_tApp_decompose in Hterm.
    destruct Hterm as [A [body [Ht_lam Ht_body]]].
    apply Htu in Ht_lam.
    assert (Hbeta : steps (tApp (tLam A body) a.[σ]) (subst0 a.[σ] body)).
    { apply steps_step. apply step_beta. }
    split.
    + eapply steps_trans. * apply steps_app1. destruct Ht_lam as [Hs _]. exact Hs.
      * eapply steps_trans. -- exact Hbeta. -- destruct Ht_body as [Hs _]. exact Hs.
    + exact (proj2 Ht_body).
  - intros σ v Hterm.
    apply terminates_to_tApp_decompose in Hterm.
    destruct Hterm as [A [body [Hu_lam Hu_body]]].
    apply Hut in Hu_lam.
    assert (Hbeta : steps (tApp (tLam A body) a.[σ]) (subst0 a.[σ] body)).
    { apply steps_step. apply step_beta. }
    split.
    + eapply steps_trans. * apply steps_app1. destruct Hu_lam as [Hs _]. exact Hs.
      * eapply steps_trans. -- exact Hbeta. -- destruct Hu_body as [Hs _]. exact Hs.
    + exact (proj2 Hu_body).
Qed.

Lemma ciu_apps (t u : tm) (args : list tm) :
  ciu t u -> ciu (apps t args) (apps u args).
Proof.
  revert t u. induction args as [|a args IH]; intros t u Hciu.
  - cbn. exact Hciu.
  - cbn. apply IH. apply ciu_tApp. exact Hciu.
Qed.

(** Branch lookup equals term at position. *)
Lemma branch_nth (brs : list tm) (c : nat) (br : tm) :
  branch brs c = Some br -> forall d, nth c brs d = br.
Proof.
  unfold branch.
  revert c br.
  induction brs as [|b brs IH]; intros [|c] br H d; cbn in H; try discriminate; cbn.
  - inversion H. reflexivity.
  - exact (IH c br H d).
Qed.

(** CIU preserved under substitution. *)
Lemma ciu_subst0 (s t u : tm) : ciu t u -> ciu (subst0 s t) (subst0 s u).
Proof.
  intro Hciu. destruct Hciu as [Htu Hut]. split.
  - intros σ v Hterm.
    unfold subst0 in Hterm |- *.
    asimpl in Hterm.
    asimpl.
    apply Htu.
    exact Hterm.
  - intros σ v Hterm.
    unfold subst0 in Hterm |- *.
    asimpl in Hterm.
    asimpl.
    apply Hut.
    exact Hterm.
Qed.

(** subst0 fix (shift (S d) t) = shift d t *)
Lemma subst0_shift_cancel (d : nat) (fix_tm t : tm) :
  subst0 fix_tm (shift (S d) 0 t) = shift d 0 t.
Proof.
  unfold subst0, shift, rename.
  repeat rewrite rename_subst.
  rewrite subst_comp.
  apply (f_equal (fun σ => t.[σ])).
  extensionality x.
  unfold scomp.
  cbn.
  unfold shift_sub.
  destruct x as [|x]; cbn; asimpl; reflexivity.
Qed.
