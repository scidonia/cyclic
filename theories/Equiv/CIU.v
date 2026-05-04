From Stdlib Require Import Utf8 List.
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
Lemma ciu_case_iota (I c args C brs br : tm) :
  branch brs c = Some br -> ciu (tCase I (tRoll I c args) C brs) (apps br args).
Proof. intro Hbr. apply step_ciu. apply step_case_roll. exact Hbr. Qed.
Lemma ciu_case_scrut_congr (I scrut scrut' C brs : tm) :
  steps scrut scrut' -> ciu (tCase I scrut C brs) (tCase I scrut' C brs).
Proof. intro Hsteps. apply steps_ciu. apply steps_case_scrut_congr. exact Hsteps. Qed.

Lemma shift_subst_eq (d : nat) (σ : var -> tm) (t : tm) :
  t.[ren (+d)].[σ] = t.[ren (+d) >>> σ].
Proof. asimpl. reflexivity. Qed.

Lemma ciu_shift (d : nat) (t u : tm) : ciu t u -> ciu (shift d 0 t) (shift d 0 u).
Proof.
  intro Hciu. destruct Hciu as [Htu Hut]. split.
  - intros σ v Hterm. apply Htu with (σ := ren (+d) >>> σ).
    rewrite <- shift_subst_eq in Hterm. exact Hterm.
  - intros σ v Hterm. apply Hut with (σ := ren (+d) >>> σ).
    rewrite <- shift_subst_eq in Hterm. exact Hterm.
Qed.

Lemma terminates_to_tApp_decompose (t a v : tm) :
  terminates_to (tApp t a) v ->
  exists A body, terminates_to t (tLam A body) /\ terminates_to (subst0 a body) v.
Proof.
  intros [Hsteps Hval].
  (* By determinism of CBN, the only way tApp... reaches a value is via beta.
     Use steps_decomp to peel off step_app1 -> eventually step_beta. *)
  revert t a Hsteps Hval.
  refine (clos_refl_trans_ind tm step _ (fun w =>
    forall t0 a0, w = tApp t0 a0 -> value v ->
    exists A body, terminates_to t0 (tLam A body) /\ terminates_to (subst0 a0 body) v) _ _).
  - intros y Hstep IH t0 a0 Heq Hv. subst.
    inversion Hstep; subst; clear Hstep.
    + exists A0, t0. split.
      * split; [apply rt_refl|apply v_lam].
      * split; [exact H0|exact Hv].
    + apply (IH t' a0 eq_refl Hv).
  - intros t0 a0 Heq Hv. subst. inversion Hv.
Qed.

Lemma ciu_tApp (t u a : tm) : ciu t u -> ciu (tApp t a) (tApp u a).
Proof.
  intro Hciu. destruct Hciu as [Htu Hut]. split.
  - intros σ v Hterm.
    apply terminates_to_tApp_decompose in Hterm.
    destruct Hterm as [A [body [Ht_lam Ht_body]]].
    apply Htu in Ht_lam.
    pose proof (step_subst σ _ _ (step_beta A body a)) as Hbeta.
    apply steps_step in Hbeta.
    split.
    + eapply steps_trans. * apply steps_app1. destruct Ht_lam as [Hs _]. exact Hs.
      * eapply steps_trans. -- exact Hbeta. -- destruct Ht_body as [Hs _]. exact Hs.
    + exact (proj2 Ht_body).
  - intros σ v Hterm.
    apply terminates_to_tApp_decompose in Hterm.
    destruct Hterm as [A [body [Hu_lam Hu_body]]].
    apply Hut in Hu_lam.
    pose proof (step_subst σ _ _ (step_beta A body a)) as Hbeta.
    apply steps_step in Hbeta.
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
  unfold branch. intro H. apply nth_error_nth_some. exact H.
Qed.

(** CIU preserved under substitution. *)
Lemma ciu_subst0 (s t u : tm) : ciu t u -> ciu (subst0 s t) (subst0 s u).
Proof.
  intro Hciu. destruct Hciu as [Htu Hut]. split.
  - intros σ v Hterm.
    apply Htu with (σ := s.:ids >>> σ).
    asimpl in Hterm. asimpl. exact Hterm.
  - intros σ v Hterm.
    apply Hut with (σ := s.:ids >>> σ).
    asimpl in Hterm. asimpl. exact Hterm.
Qed.

(** subst0 fix (shift (S d) t) = shift d t *)
Lemma subst0_shift_cancel (d : nat) (fix_tm t : tm) :
  subst0 fix_tm (shift (S d) 0 t) = shift d 0 t.
Proof.
  asimpl. reflexivity.
Qed.
  length orig_brs = length res_brs ->
  (forall c, c < length orig_brs -> ciu (nth c orig_brs (tVar 0)) (nth c res_brs (tVar 0))) ->
  ciu (tCase I (tVar x) Cmot orig_brs) (tCase I (tVar x) Cmot res_brs).
Proof.
  intros Hlen Hbrs. split.
  - intros σ v Hterm.
    asimpl in Hterm.
    apply terminates_to_tCase_decompose in Hterm.
    destruct Hterm as [c [args [br [Hscrut [Hb Hbody]]]]].
    apply branch_nth with (d := tVar 0) in Hb.
    assert (Hc_len : c < length orig_brs).
    { apply nth_error_Some_length. unfold branch in Hb. 
      rewrite nth_error_map in Hb. destruct (nth_error orig_brs c); [|discriminate].
      apply nth_error_Some. lia. }
    pose proof (Hbrs c Hc_len) as Hci.
    apply (ciu_apps _ _ args) in Hci. destruct Hci as [Hto _].
    apply Hto with (σ' := σ) in Hbody.
    destruct Hscrut as [Hs_sv Hval_s].
    assert (Hbr_res : branch (map (fun t0 : tm => t0.[σ]) res_brs) c
                     = Some (nth c (map (fun t0 : tm => t0.[σ]) res_brs) (tVar 0))).
    { unfold branch. rewrite nth_error_nth'. apply nth_error_nth. exact I. }
    (* Actually: nth_error_map gives the direct equality *)
    rewrite nth_error_map. simpl.
    pose proof (nth_error_nth' res_brs c (tVar 0)) as Hnth.
    destruct (nth_error res_brs c) eqn:Hres.
    - simpl. f_equal. rewrite Hnth. reflexivity.
    - (* branch doesn't exist at position c, but by length equality and CIU,
         this case cannot arise when the orig branch exists.
         Actually: Hb says branch (map ... orig_brs) c = Some (nth c ...).[σ].
         This implies nth_error orig_brs c is Some. By Hlen, nth_error res_brs c is also Some
         OR the res branch is shorter. But we assumed lengths are equal. *)
      apply nth_error_Some_length in Hres. 2: { }
    apply nth_error_None in Hres. lia. *)
      exfalso. apply (nth_error_None _ _ Hres). rewrite Hlen.
      apply nth_error_Some_length. unfold branch in Hb. rewrite nth_error_map in Hb.
      destruct (nth_error orig_brs c) eqn:Horig; [|discriminate].
      exists t0. exact Horig.
    }
    apply (steps_case_to_apps I (σ x) (Cmot.[σ]) (map (fun t0 => t0.[σ]) res_brs) c args
             (nth c (map (fun t0 : tm => t0.[σ]) res_brs) (tVar 0))) in Hs_sv; [|exact Hbr_res].
    split. + eapply steps_trans; [exact Hs_sv|destruct Hbody as [Hs _]; rewrite <- Hb in Hs; exact Hs].
    + exact (proj2 Hbody).
  - intros σ v Hterm. a symmetric version of the above, using the symmetric CIU direction. *)
    asimpl in Hterm.
    apply terminates_to_tCase_decompose in Hterm.
    destruct Hterm as [c [args [br [Hscrut [Hb Hbody]]]]].
    apply branch_nth with (d := tVar 0) in Hb.
    assert (Hc_len : c < length res_brs).
    { unfold branch in Hb. rewrite nth_error_map in Hb.
      destruct (nth_error res_brs c); [|discriminate].
      apply nth_error_Some. lia. }
    rewrite Hlen in Hc_len.
    pose proof (Hbrs c Hc_len) as Hci.
    apply (ciu_apps _ _ args) in Hci. destruct Hci as [_ Hfrom].
    apply Hfrom with (σ' := σ) in Hbody.
    destruct Hscrut as [Hs_sv Hval_s].
    assert (Hbr_orig : branch (map (fun t0 : tm => t0.[σ]) orig_brs) c
                     = Some (nth c (map (fun t0 : tm => t0.[σ]) orig_brs) (tVar 0))).
    { rewrite nth_error_map. simpl.
      destruct (nth_error orig_brs c) eqn:Horig.
      - simpl. f_equal. apply nth_error_nth' with (d := tVar 0) in Horig. exact Horig.
      - exfalso.
        apply nth_error_None in Horig.
        assert (Hres_len : nth_error res_brs c <> None).
        { unfold branch in Hb. rewrite nth_error_map in Hb.
          destruct (nth_error res_brs c); [discriminate|discriminate]. }
        apply Hres_len. apply nth_error_None.
        rewrite <- Hlen. exact Horig.
    }
    apply (steps_case_to_apps I (σ x) (Cmot.[σ]) (map (fun t0 => t0.[σ]) orig_brs) c args
             (nth c (map (fun t0 : tm => t0.[σ]) orig_brs) (tVar 0))) in Hs_sv; [|exact Hbr_orig].
    split. + eapply steps_trans; [exact Hs_sv|destruct Hbody as [Hs _]; exact Hs].
    + exact (proj2 Hbody).
Qed.
