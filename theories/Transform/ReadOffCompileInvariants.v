From Stdlib Require Import List Lia.
From stdpp Require Import prelude gmap.

From Cyclic.Syntax Require Import Term.
From Cyclic.Transform Require Import ReadOff.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module RO := ReadOff.

Section CompileInvariants.

  Lemma build_subst_chain_bnext_mono (us : list nat) (sv_tail : nat) (b : RO.builder) :
    RO.b_next b <= RO.b_next (snd (RO.build_subst_chain us sv_tail b)).
  Proof.
    revert b.
    induction us as [|u us IH]; intro b; simpl.
    - lia.
    - destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
      specialize (IH b).
      rewrite Hch in IH.
      unfold RO.fresh.
      simpl.
      eapply Nat.le_trans; [exact IH|].
      apply Nat.le_succ_diag_r.
  Qed.

  Lemma compile_tm_bnext_mono
      (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
    RO.b_next b <= RO.b_next (snd (RO.compile_tm fuel ρ t b))
  with compile_list_bnext_mono
      (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
    RO.b_next b <= RO.b_next (snd (RO.compile_list fuel ρ ts b)).
  Proof.
    - revert ρ t b.
      induction fuel as [|fuel IH]; intros ρ t b; simpl.
      + unfold RO.fresh. simpl. lia.
      + destruct t as [x|i|A B|A t0|t1 t2|A body|ind0|ind1 ctor params recs|ind2 scrut C brs]; simpl;
          try (unfold RO.fresh; simpl; lia).
        * (* tPi *)
          destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
          pose proof (IH ρ A b) as HmA.
          rewrite HA in HmA.
          destruct (RO.compile_tm fuel (None :: ρ) B b1) as [vB b2] eqn:HB.
          pose proof (IH (None :: ρ) B b1) as HmB.
          rewrite HB in HmB.
          unfold RO.fresh, RO.put. simpl.
          eapply Nat.le_trans; [exact HmA|].
          eapply Nat.le_trans; [exact HmB|].
          apply Nat.le_succ_diag_r.
        * (* tLam *)
          destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
          pose proof (IH ρ A b) as HmA.
          rewrite HA in HmA.
          destruct (RO.compile_tm fuel (None :: ρ) t0 b1) as [vt b2] eqn:HB.
          pose proof (IH (None :: ρ) t0 b1) as HmB.
          rewrite HB in HmB.
          unfold RO.fresh, RO.put. simpl.
          eapply Nat.le_trans; [exact HmA|].
          eapply Nat.le_trans; [exact HmB|].
          apply Nat.le_succ_diag_r.
        * (* tApp *)
          destruct (RO.app_view t1) as [h args] eqn:Hv.
          set (args_full := args ++ [t2]).
          destruct h as [x|i|A0 B0|A0 t0|h1 h2|A0 body0|indh|indh ctorh paramsh recsh|indh scruth Ch brsh];
            try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
                 pose proof (IH ρ t1 b) as Hm1; rewrite H1 in Hm1;
                 destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
                 pose proof (IH ρ t2 b1) as Hm2; rewrite H2 in Hm2;
                 unfold RO.fresh, RO.put; simpl; lia).
          (* head is var: check environment for backlink target *)
          destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
            try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
                 pose proof (IH ρ t1 b) as Hm1; rewrite H1 in Hm1;
                 destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
                 pose proof (IH ρ t2 b1) as Hm2; rewrite H2 in Hm2;
                 unfold RO.fresh, RO.put; simpl; lia).
          (* backlink case *)
          destruct (RO.compile_list fuel ρ args_full b) as [v_args b1] eqn:Hargs.
          pose proof (compile_list_bnext_mono fuel ρ args_full b) as Hmargs.
          rewrite Hargs in Hmargs.
          destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfr1.
          set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
          destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
          pose proof (build_subst_chain_bnext_mono v_args sv_nil b3) as Hbmn.
          rewrite Hch in Hbmn.
          destruct (RO.fresh b4) as [v b5] eqn:Hfr2.
          (* simplify the goal's nested lets *)
          rewrite Hargs, Hfr1, Hch, Hfr2.
          unfold b3 in *.
          unfold RO.fresh, RO.put in *.
          simpl in *.
          lia.
        * (* tFix *)
          destruct (RO.fresh b) as [v b0] eqn:Hfr.
          simpl in *.
          destruct (RO.compile_tm fuel ρ A b0) as [vA b1] eqn:HA.
          pose proof (IH ρ A b0) as HmA.
          rewrite HA in HmA.
          set (b1' := RO.put_fix_ty v vA b1).
          destruct (RO.compile_tm fuel (Some v :: ρ) body b1') as [vbody b2] eqn:HB.
          pose proof (IH (Some v :: ρ) body b1') as HmB.
          rewrite HB in HmB.
          (* final put does not change b_next *)
          subst b1'. simpl in *.
          lia.
        * (* tRoll *)
          destruct (RO.compile_list fuel ρ params b) as [vps b1] eqn:Hps.
          pose proof (compile_list_bnext_mono fuel ρ params b) as Hmps.
          rewrite Hps in Hmps.
          destruct (RO.compile_list fuel ρ recs b1) as [vrs b2] eqn:Hrs.
          pose proof (compile_list_bnext_mono fuel ρ recs b1) as Hmrs.
          rewrite Hrs in Hmrs.
          unfold RO.fresh. simpl. lia.
        * (* tCase *)
          destruct (RO.compile_tm fuel ρ scrut b) as [vscrut b1] eqn:Hs.
          pose proof (IH ρ scrut b) as Hms. rewrite Hs in Hms.
          destruct (RO.compile_tm fuel ρ C b1) as [vC b2] eqn:Hc.
          pose proof (IH ρ C b1) as Hmc. rewrite Hc in Hmc.
          destruct (RO.compile_list fuel ρ brs b2) as [vbrs b3] eqn:Hbrs.
          pose proof (compile_list_bnext_mono fuel ρ brs b2) as Hmbrs.
          rewrite Hbrs in Hmbrs.
          unfold RO.fresh. simpl. lia.
    - revert b ts.
      induction fuel as [|fuel IH]; intros b ts; simpl.
      + lia.
      + destruct ts as [|t ts]; [lia|].
        destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
        pose proof (compile_tm_bnext_mono fuel ρ t b) as Hm.
        rewrite Ht in Hm.
        specialize (IH b1 ts).
        lia.
  Qed.

  Lemma compile_tm_root_lt
      (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
    fst (RO.compile_tm fuel ρ t b) < RO.b_next (snd (RO.compile_tm fuel ρ t b)).
  Proof.
    revert ρ t b.
    induction fuel as [|fuel IH]; intros ρ t b; simpl.
    - unfold RO.fresh. simpl. lia.
    - destruct t; simpl;
        try (unfold RO.fresh; simpl; lia).
      + (* tPi *)
        destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
        destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2] eqn:HB.
        unfold RO.fresh. simpl. lia.
      + (* tLam *)
        destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
        destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2] eqn:HB.
        unfold RO.fresh. simpl. lia.
      + (* tApp *)
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h; [| | | | | | | |];
          try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
               destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
               unfold RO.fresh; simpl; lia).
        destruct (nth_error ρ n) as [[target|]|] eqn:Hnth;
          try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
               destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
               unfold RO.fresh; simpl; lia).
        destruct (RO.compile_list fuel ρ args b) as [v_args b1] eqn:Hargs.
        unfold RO.fresh. simpl. lia.
      + (* tFix *)
        destruct (RO.fresh b) as [v b0] eqn:Hfr.
        destruct (RO.compile_tm fuel ρ t1 b0) as [vA b1] eqn:HA.
        set (b1' := RO.put_fix_ty v vA b1).
        destruct (RO.compile_tm fuel (Some v :: ρ) t2 b1') as [vbody b2] eqn:HB.
        pose proof (compile_tm_bnext_mono fuel ρ t1 b0) as HbA.
        rewrite HA in HbA.
        pose proof (compile_tm_bnext_mono fuel (Some v :: ρ) t2 b1') as HbB.
        rewrite HB in HbB.
        unfold RO.fresh in Hfr. simpl in Hfr.
        inversion Hfr; subst v b0.
        simpl in *.
        lia.
      + (* tRoll *)
        destruct (RO.compile_list fuel ρ l b) as [vps b1] eqn:Hps.
        destruct (RO.compile_list fuel ρ l0 b1) as [vrs b2] eqn:Hrs.
        unfold RO.fresh. simpl. lia.
      + (* tCase *)
        destruct (RO.compile_tm fuel ρ t1 b) as [vscrut b1] eqn:Hs.
        destruct (RO.compile_tm fuel ρ t2 b1) as [vC b2] eqn:Hc.
        destruct (RO.compile_list fuel ρ l b2) as [vbrs b3] eqn:Hbrs.
        unfold RO.fresh. simpl. lia.
  Qed.

  Lemma compile_list_roots_lt
      (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
    Forall (fun v => v < RO.b_next (snd (RO.compile_list fuel ρ ts b)))
      (fst (RO.compile_list fuel ρ ts b)).
  Proof.
    revert b ts.
    induction fuel as [|fuel IH]; intros b ts; simpl.
    - constructor.
    - destruct ts as [|t ts]; [constructor|].
      destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
      destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
      simpl.
      constructor.
      + pose proof (compile_tm_root_lt fuel ρ t b) as Hv.
        rewrite Ht in Hv.
        pose proof (compile_list_bnext_mono fuel ρ ts b1) as Hmn.
        rewrite Hts in Hmn.
        lia.
      + specialize (IH b1 ts).
        rewrite Hts in IH.
        exact IH.
  Qed.

End CompileInvariants.
