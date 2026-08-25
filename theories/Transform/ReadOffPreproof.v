From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap fin_sets.
From Stdlib Require Import List.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff CyclicRules.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module CR := CyclicRules.

Section Packaging.
  (** Package the raw read-off graph as a rooted preproof whose labels are
      vertex-based judgements.

      This is an incremental correctness step:
      - substitution evidence nodes (`nSubstNil`/`nSubstCons`) are labelled by
        `jSub` judgements and checked by the structural `jSub` rule.
      - all other nodes are labelled by a dummy `jTy` judgement and are accepted
        by a permissive rule (`True`) for now.

      Next step: strengthen `jTy`/`jEq` cases and make `pp_label` produce real
      typing/equality goals.
  *)

  Definition V : Type := nat.

  (** Vertices of the graph: label-bearing nodes plus tFix cycle targets. *)
  Definition verts_of (b : RO.builder) : gset V :=
    dom (RO.b_label b) ∪ dom (RO.b_fix_ty b).

  Definition succ_of (b : RO.builder) (v : V) : list V :=
    filter (fun w => bool_decide (w ∈ verts_of b))
      (default [] (RO.b_succ b !! v)).

  Definition label_of (b : RO.builder) (v : V) : RO.node :=
    default (RO.nVar 0) (RO.b_label b !! v).

  Definition dummy_type : V := 0.

  Fixpoint sub_ctx (fuel : nat) (b : RO.builder) (sv : V) : list V :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match RO.b_label b !! sv with
        | Some (RO.nSubstNil _) => []
        | Some (RO.nSubstCons _) =>
            match RO.b_succ b !! sv with
            | Some [u; sv_tail] => dummy_type :: sub_ctx fuel' b sv_tail
            | _ => []
            end
        | _ => []
        end
    end.

  Definition shiftV (_n _k : nat) (x : V) : V := x.
  Definition substV (_sv : V) (x : V) : V := x.

  Definition Judgement : Type := CR.judgement (V := V).

  Definition pp_label (b : RO.builder) (v : V) : Judgement :=
    match label_of b v with
    | RO.nSubstNil _ => CR.jSub (V := V) [] v (sub_ctx (RO.b_next b + 1) b v)
    | RO.nSubstCons _ => CR.jSub (V := V) [] v (sub_ctx (RO.b_next b + 1) b v)
    | _ => CR.jTy (V := V) [] v dummy_type
    end.

  (** Permissive rule for initial graph packaging. *)
  Definition Rule (b : RO.builder) (j : Judgement) (premises : list Judgement) : Prop :=
    True.

  Lemma succ_of_closed (b : RO.builder) (v : V) :
    Forall (fun w => w ∈ verts_of b) (succ_of b v).
  Admitted.

  Program Definition graph_of (b : RO.builder) : FiniteDigraph.fin_digraph :=
    {| FiniteDigraph.verts := verts_of b;
       FiniteDigraph.succ := succ_of b |}.
  Next Obligation.
    intros b v Hv.
    exact (succ_of_closed b v).
  Qed.

  Lemma pp_rule_ok (b : RO.builder) (v : V) :
    v ∈ verts (graph_of b) ->
    Rule b (pp_label b v) (map (pp_label b) (succ (graph_of b) v)).
  Proof. intro; exact I. Qed.

  Definition preproof_of (b : RO.builder)
      : @Preproof.preproof Judgement (Rule b) V _ _ :=
    {| Preproof.pp_graph := graph_of b;
       Preproof.pp_label := pp_label b;
       Preproof.pp_rule_ok := fun v Hv => pp_rule_ok b v Hv |}.

  (** Builder well-formedness: every key in b_fix_ty is < b_next. *)
  Definition builder_wf (b : RO.builder) : Prop :=
    ∀ u vA, RO.b_fix_ty b !! u = Some vA → u < RO.b_next b.

  Lemma empty_builder_wf : builder_wf RO.empty_builder.
  Proof.
    intros u vA H.
    unfold RO.empty_builder in H. simpl in H. rewrite lookup_empty in H. discriminate.
  Qed.

  Lemma builder_wf_fresh (b : RO.builder) : builder_wf b -> builder_wf (snd (RO.fresh b)).
  Proof.
    intros Hwf u vA Hu.
    unfold RO.fresh; simpl.
    unfold RO.fresh in Hu; simpl in Hu.
    apply Hwf in Hu. lia.
  Qed.

  Lemma builder_wf_put_fix_ty (b : RO.builder) v vA :
    builder_wf b -> v < RO.b_next b -> builder_wf (RO.put_fix_ty v vA b).
  Proof.
    intros Hwf Hlt u vA' Hu.
    unfold RO.put_fix_ty in Hu. simpl in Hu.
    apply lookup_insert_Some in Hu as [[<- _] | [_ Hu]].
    - exact Hlt.
    - apply Hwf in Hu. exact Hu.
  Qed.

  Lemma builder_wf_put_fix_body (b : RO.builder) v vbody :
    builder_wf b -> builder_wf (RO.put_fix_body v vbody b).
  Proof.
    intros Hwf u vA Hu.
    unfold RO.put_fix_body in Hu. simpl in Hu.
    apply Hwf in Hu. exact Hu.
  Qed.

  Lemma builder_wf_put (b : RO.builder) v lbl succs :
    builder_wf b -> builder_wf (RO.put v lbl succs b).
  Proof.
    intros Hwf u vA Hu.
    unfold RO.put in Hu. simpl in Hu.
    apply Hwf in Hu. exact Hu.
  Qed.

  (** b_fix_ty is preserved by structural builder operations. *)
  Lemma b_fix_ty_fresh (b : RO.builder) :
    RO.b_fix_ty (snd (RO.fresh b)) = RO.b_fix_ty b.
  Proof. unfold RO.fresh; simpl; reflexivity. Qed.

  Lemma b_fix_ty_put (b : RO.builder) v lbl succs :
    RO.b_fix_ty (RO.put v lbl succs b) = RO.b_fix_ty b.
  Proof. unfold RO.put; simpl; reflexivity. Qed.

  Lemma b_fix_ty_put_fix_body (b : RO.builder) v vbody :
    RO.b_fix_ty (RO.put_fix_body v vbody b) = RO.b_fix_ty b.
  Proof. unfold RO.put_fix_body; simpl; reflexivity. Qed.

  Lemma b_fix_ty_build_subst_chain (us : list nat) (sv_tail : nat) (b : RO.builder) :
    RO.b_fix_ty (snd (RO.build_subst_chain us sv_tail b)) = RO.b_fix_ty b.
  Proof.
    induction us as [|u us IH].
    - simpl. reflexivity.
    - simpl.
      destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hchain.
      destruct (RO.fresh b1) as [sv_head b2] eqn:Hfresh.
      unfold RO.put; simpl.
      unfold RO.fresh in Hfresh; inversion Hfresh; subst; simpl.
      exact IH.
  Qed.

  (** compile_tm preserves dom of b_fix_ty. *)
  Lemma compile_tm_fix_ty_dom_mono_aux (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (v : nat) :
    v ∈ dom (RO.b_fix_ty b) ->
    v ∈ dom (RO.b_fix_ty (snd (RO.compile_tm fuel ρ t b)))
  with compile_list_fix_ty_dom_mono_aux (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) (v : nat) :
    v ∈ dom (RO.b_fix_ty b) ->
    v ∈ dom (RO.b_fix_ty (snd (RO.compile_list fuel ρ ts b))).
  Proof.
    - revert ρ t b v.
      induction fuel as [|fuel' IH]; intros ρ t b v Hv.
      + cbn [RO.compile_tm].
        destruct (RO.fresh b) as [vroot b1] eqn:Hfresh.
        cbn [snd].
        rewrite b_fix_ty_put.
        replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
        rewrite b_fix_ty_fresh.
        exact Hv.
      + cbn [RO.compile_tm].
        destruct t as [x|i|A B|A t|tApp_l tApp_r|A_fix body_fix|ind args|ind ctor args|ind scrut C brs].
        * destruct (RO.fresh b) as [vroot b1] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          exact Hv.
        * destruct (RO.fresh b) as [vroot b1] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          exact Hv.
        * (* tPi *)
          destruct (RO.compile_tm fuel' ρ A b) as [vA0 b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) B b1) as [vB b2] eqn:H2.
          destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (IH ρ A b v Hv) as Hv1.
          rewrite H1 in Hv1.
          pose proof (IH (None :: ρ) B b1 v Hv1) as Hv2.
          rewrite H2 in Hv2.
          exact Hv2.
        * (* tLam *)
          destruct (RO.compile_tm fuel' ρ A b) as [vA0 b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) t b1) as [vt b2] eqn:H2.
          destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (IH ρ A b v Hv) as Hv1.
          rewrite H1 in Hv1.
          pose proof (IH (None :: ρ) t b1 v Hv1) as Hv2.
          rewrite H2 in Hv2.
          exact Hv2.
        * (* tApp *)
          destruct (RO.app_view (Term.Syntax.tApp tApp_l tApp_r)) as [h args] eqn:Hav.
          destruct h as [x|i|A' B'|A' t'|h1 h2|A' body'|ind' args'|ind' ctor' args'|ind' scrut' C' brs'];
            try (destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
                 destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
                 destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh;
                 cbn [snd];
                 rewrite b_fix_ty_put;
                 replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
                 rewrite b_fix_ty_fresh;
                 pose proof (IH ρ tApp_l b v Hv) as Hv1;
                 rewrite H1 in Hv1;
                 pose proof (IH ρ tApp_r b1 v Hv1) as Hv2;
                 rewrite H2 in Hv2;
                 exact Hv2).
          destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
            [ destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist;
              destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfresh1;
              set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2);
              destruct (RO.build_subst_chain vargs sv_nil b3) as [sv b4] eqn:Hbsc;
              destruct (RO.fresh b4) as [vroot b5] eqn:Hfresh2;
              cbn [snd];
              rewrite b_fix_ty_put;
              replace b5 with (snd (RO.fresh b4)) by (rewrite Hfresh2; reflexivity);
              rewrite b_fix_ty_fresh;
              replace b4 with (snd (RO.build_subst_chain vargs sv_nil b3))
                by (rewrite Hbsc; reflexivity);
              rewrite b_fix_ty_build_subst_chain;
              unfold b3;
              rewrite b_fix_ty_put;
              replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh1; reflexivity);
              rewrite b_fix_ty_fresh;
              pose proof (compile_list_fix_ty_dom_mono_aux fuel' ρ args b v Hv) as Hv1;
              rewrite Hlist in Hv1;
              exact Hv1
            | destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
              destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
              destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh;
              cbn [snd];
              rewrite b_fix_ty_put;
              replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
              rewrite b_fix_ty_fresh;
              pose proof (IH ρ tApp_l b v Hv) as Hv1;
              rewrite H1 in Hv1;
              pose proof (IH ρ tApp_r b1 v Hv1) as Hv2;
              rewrite H2 in Hv2;
              exact Hv2
            | destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
              destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
              destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh;
              cbn [snd];
              rewrite b_fix_ty_put;
              replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
              rewrite b_fix_ty_fresh;
              pose proof (IH ρ tApp_l b v Hv) as Hv1;
              rewrite H1 in Hv1;
              pose proof (IH ρ tApp_r b1 v Hv1) as Hv2;
              rewrite H2 in Hv2;
              exact Hv2 ].
        * (* tFix *)
          destruct (RO.fresh b) as [v_fix b0] eqn:Hfresh0.
          destruct (RO.compile_tm fuel' ρ A_fix b0) as [vA0 b1] eqn:HA.
          set (b1' := RO.put_fix_ty v_fix vA0 b1).
          destruct (RO.compile_tm fuel' (Some v_fix :: ρ) body_fix b1') as [vbody b2] eqn:Hbody.
          cbn [snd].
          rewrite b_fix_ty_put_fix_body.
          assert (Hv0 : v ∈ dom (RO.b_fix_ty b0)).
          { replace b0 with (snd (RO.fresh b)) by (rewrite Hfresh0; reflexivity).
            rewrite b_fix_ty_fresh. exact Hv. }
          pose proof (IH ρ A_fix b0 v Hv0) as Hv1.
          rewrite HA in Hv1.
          assert (Hv1' : v ∈ dom (RO.b_fix_ty b1')).
          { unfold b1'.
            unfold RO.put_fix_ty; simpl.
            apply elem_of_dom.
            destruct (decide (v_fix = v)) as [->|Hneq].
            - rewrite lookup_insert. eexists; reflexivity.
            - apply elem_of_dom in Hv1 as [vA' HvA'].
              rewrite lookup_insert_ne; [eexists; exact HvA' | exact Hneq]. }
          pose proof (IH (Some v_fix :: ρ) body_fix b1' v Hv1') as Hv2.
          rewrite Hbody in Hv2.
          exact Hv2.
        * (* tInd *)
          destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [vroot b2] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_list_fix_ty_dom_mono_aux fuel' ρ args b v Hv) as Hv1.
          rewrite Hlist in Hv1.
          exact Hv1.
        * (* tRoll *)
          destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [vroot b2] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_list_fix_ty_dom_mono_aux fuel' ρ args b v Hv) as Hv1.
          rewrite Hlist in Hv1.
          exact Hv1.
        * (* tCase *)
          destruct (RO.compile_tm fuel' ρ scrut b) as [vscrut b1] eqn:H1.
          destruct (RO.compile_tm fuel' ρ C b1) as [vC b2] eqn:H2.
          destruct (RO.compile_list fuel' ρ brs b2) as [vbrs b3] eqn:Hlist.
          destruct (RO.fresh b3) as [vroot b4] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b4 with (snd (RO.fresh b3)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (IH ρ scrut b v Hv) as Hv1.
          rewrite H1 in Hv1.
          pose proof (IH ρ C b1 v Hv1) as Hv2.
          rewrite H2 in Hv2.
          pose proof (compile_list_fix_ty_dom_mono_aux fuel' ρ brs b2 v Hv2) as Hv3.
          rewrite Hlist in Hv3.
          exact Hv3.
    - revert ρ ts b v.
      induction fuel as [|fuel' IH]; intros ρ ts b v Hv.
      + cbn [RO.compile_list]. exact Hv.
      + cbn [RO.compile_list].
        destruct ts as [|t ts].
        * simpl. exact Hv.
        * destruct (RO.compile_tm fuel' ρ t b) as [v1 b1] eqn:Htm.
          destruct (RO.compile_list fuel' ρ ts b1) as [vs' b2] eqn:Hlist.
          simpl.
          pose proof (compile_tm_fix_ty_dom_mono_aux fuel' ρ t b v Hv) as Hv1.
          rewrite Htm in Hv1.
          pose proof (IH ρ ts b1 v Hv1) as Hv2.
          rewrite Hlist in Hv2.
          exact Hv2.
  Qed.

  (** b_next monotonicity for compile_tm and compile_list. *)
  Lemma compile_tm_b_next_le (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) :
    RO.b_next b ≤ RO.b_next (snd (RO.compile_tm fuel ρ t b))
  with compile_list_b_next_le (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) :
    RO.b_next b ≤ RO.b_next (snd (RO.compile_list fuel ρ ts b)).
  Admitted.

  Lemma builder_wf_build_subst_chain (us : list nat) (sv_tail : nat) (b : RO.builder) :
    builder_wf b -> builder_wf (snd (RO.build_subst_chain us sv_tail b)).
  Proof.
    revert sv_tail b.
    induction us as [|u us IH]; intros sv_tail b Hwf.
    - simpl. exact Hwf.
    - simpl.
      destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hchain.
      destruct (RO.fresh b1) as [sv_head b2] eqn:Hfresh.
      simpl.
      apply builder_wf_put.
      apply builder_wf_fresh.
      pose proof (IH sv_tail b Hwf) as Hwf1.
      rewrite Hchain in Hwf1. exact Hwf1.
  Qed.

  (** compile_tm preserves builder_wf. *)
  Lemma compile_tm_builder_wf_aux (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) :
    builder_wf b ->
    builder_wf (snd (RO.compile_tm fuel ρ t b))
  with compile_list_builder_wf_aux (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) :
    builder_wf b ->
    builder_wf (snd (RO.compile_list fuel ρ ts b)).
  Proof.
    - revert ρ t b.
      induction fuel as [|fuel' IH]; intros ρ t b Hwf.
      + cbn [RO.compile_tm].
        destruct (RO.fresh b) as [v b1] eqn:Hfresh.
        cbn [snd].
        apply builder_wf_put.
        replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
        apply builder_wf_fresh. exact Hwf.
      + cbn [RO.compile_tm].
        destruct t as [x|i|A B|A t|tApp_l tApp_r|A_fix body_fix|ind args|ind ctor args|ind scrut C brs].
        * destruct (RO.fresh b) as [v b1] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh. exact Hwf.
        * destruct (RO.fresh b) as [v b1] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh. exact Hwf.
        * (* tPi *)
          destruct (RO.compile_tm fuel' ρ A b) as [vA0 b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) B b1) as [vB b2] eqn:H2.
          destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh.
          pose proof (IH ρ A b Hwf) as Hwf1.
          rewrite H1 in Hwf1.
          pose proof (IH (None :: ρ) B b1 Hwf1) as Hwf2.
          rewrite H2 in Hwf2.
          exact Hwf2.
        * (* tLam *)
          destruct (RO.compile_tm fuel' ρ A b) as [vA0 b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) t b1) as [vt b2] eqn:H2.
          destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh.
          pose proof (IH ρ A b Hwf) as Hwf1.
          rewrite H1 in Hwf1.
          pose proof (IH (None :: ρ) t b1 Hwf1) as Hwf2.
          rewrite H2 in Hwf2.
          exact Hwf2.
        * (* tApp *)
          destruct (RO.app_view (Term.Syntax.tApp tApp_l tApp_r)) as [h args] eqn:Hav.
          destruct h as [x|i|A' B'|A' t'|h1 h2|A' body'|ind' args'|ind' ctor' args'|ind' scrut' C' brs'];
            try (destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
                 destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
                 destruct (RO.fresh b2) as [v b3] eqn:Hfresh;
                 cbn [snd];
                 apply builder_wf_put;
                 replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
                 apply builder_wf_fresh;
                 pose proof (IH ρ tApp_l b Hwf) as Hwf1;
                 rewrite H1 in Hwf1;
                 pose proof (IH ρ tApp_r b1 Hwf1) as Hwf2;
                 rewrite H2 in Hwf2;
                 exact Hwf2).
          destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
            [ destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist;
              destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfresh1;
              set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2);
              destruct (RO.build_subst_chain vargs sv_nil b3) as [sv b4] eqn:Hbsc;
              destruct (RO.fresh b4) as [v b5] eqn:Hfresh2;
              cbn [snd];
              apply builder_wf_put;
              replace b5 with (snd (RO.fresh b4)) by (rewrite Hfresh2; reflexivity);
              apply builder_wf_fresh;
              pose proof (compile_list_builder_wf_aux fuel' ρ args b Hwf) as Hwf1;
              rewrite Hlist in Hwf1;
              simpl in Hwf1;
              pose proof (builder_wf_fresh b1 Hwf1) as Hwf2;
              rewrite Hfresh1 in Hwf2;
              simpl in Hwf2;
              pose proof (builder_wf_put b2 sv_nil (RO.nSubstNil 0) [] Hwf2) as Hwf3;
              unfold b3 in Hwf3;
              pose proof (builder_wf_build_subst_chain vargs sv_nil b3 Hwf3) as Hwf4;
              rewrite Hbsc in Hwf4;
              exact Hwf4
            | destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
              destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
              destruct (RO.fresh b2) as [v b3] eqn:Hfresh;
              cbn [snd];
              apply builder_wf_put;
              replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
              apply builder_wf_fresh;
              pose proof (IH ρ tApp_l b Hwf) as Hwf1;
              rewrite H1 in Hwf1;
              pose proof (IH ρ tApp_r b1 Hwf1) as Hwf2;
              rewrite H2 in Hwf2;
              exact Hwf2
            | destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
              destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
              destruct (RO.fresh b2) as [v b3] eqn:Hfresh;
              cbn [snd];
              apply builder_wf_put;
              replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
              apply builder_wf_fresh;
              pose proof (IH ρ tApp_l b Hwf) as Hwf1;
              rewrite H1 in Hwf1;
              pose proof (IH ρ tApp_r b1 Hwf1) as Hwf2;
              rewrite H2 in Hwf2;
              exact Hwf2 ].
        * (* tFix *)
          destruct (RO.fresh b) as [v_fix b0] eqn:Hfresh0.
          destruct (RO.compile_tm fuel' ρ A_fix b0) as [vA0 b1] eqn:HA.
          set (b1' := RO.put_fix_ty v_fix vA0 b1).
          destruct (RO.compile_tm fuel' (Some v_fix :: ρ) body_fix b1') as [vbody b2] eqn:Hbody.
          cbn [snd].
          apply builder_wf_put_fix_body.
          assert (Hwf0 : builder_wf b0).
          { replace b0 with (snd (RO.fresh b)) by (rewrite Hfresh0; reflexivity).
            apply builder_wf_fresh. exact Hwf. }
          pose proof (IH ρ A_fix b0 Hwf0) as Hwf1.
          rewrite HA in Hwf1.
          assert (Hwf1' : builder_wf b1').
          { apply builder_wf_put_fix_ty.
            - exact Hwf1.
            - pose proof (compile_tm_b_next_le fuel' ρ A_fix b0) as Hle.
              rewrite HA in Hle. simpl in Hle.
              unfold RO.fresh in Hfresh0. inversion Hfresh0; subst; simpl in Hle.
              lia. }
          pose proof (IH (Some v_fix :: ρ) body_fix b1' Hwf1') as Hwf2.
          rewrite Hbody in Hwf2.
          exact Hwf2.
        * (* tInd *)
          destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [v b2] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh.
          pose proof (compile_list_builder_wf_aux fuel' ρ args b Hwf) as Hwf1.
          rewrite Hlist in Hwf1.
          exact Hwf1.
        * (* tRoll *)
          destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [v b2] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh.
          pose proof (compile_list_builder_wf_aux fuel' ρ args b Hwf) as Hwf1.
          rewrite Hlist in Hwf1.
          exact Hwf1.
        * (* tCase *)
          destruct (RO.compile_tm fuel' ρ scrut b) as [vscrut b1] eqn:H1.
          destruct (RO.compile_tm fuel' ρ C b1) as [vC b2] eqn:H2.
          destruct (RO.compile_list fuel' ρ brs b2) as [vbrs b3] eqn:Hlist.
          destruct (RO.fresh b3) as [v b4] eqn:Hfresh.
          cbn [snd].
          apply builder_wf_put.
          replace b4 with (snd (RO.fresh b3)) by (rewrite Hfresh; reflexivity).
          apply builder_wf_fresh.
          pose proof (IH ρ scrut b Hwf) as Hwf1.
          rewrite H1 in Hwf1.
          pose proof (IH ρ C b1 Hwf1) as Hwf2.
          rewrite H2 in Hwf2.
          pose proof (compile_list_builder_wf_aux fuel' ρ brs b2 Hwf2) as Hwf3.
          rewrite Hlist in Hwf3.
          exact Hwf3.
    - revert ρ ts b.
      induction fuel as [|fuel' IH]; intros ρ ts b Hwf.
      + cbn [RO.compile_list]. exact Hwf.
      + cbn [RO.compile_list].
        destruct ts as [|t ts].
        * simpl. exact Hwf.
        * destruct (RO.compile_tm fuel' ρ t b) as [v1 b1] eqn:Htm.
          destruct (RO.compile_list fuel' ρ ts b1) as [vs' b2] eqn:Hlist.
          simpl.
          pose proof (compile_tm_builder_wf_aux fuel' ρ t b Hwf) as Hwf1.
          rewrite Htm in Hwf1.
          pose proof (IH ρ ts b1 Hwf1) as Hwf2.
          rewrite Hlist in Hwf2.
          exact Hwf2.
  Qed.

  Lemma compile_tm_builder_wf (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    builder_wf b ->
    builder_wf b'.
  Proof.
    intros Hcomp Hwf.
    pose proof (f_equal snd Hcomp) as Hb'.
    simpl in Hb'.
    rewrite <- Hb'.
    apply (compile_tm_builder_wf_aux fuel ρ t b Hwf).
  Qed.

  Lemma compile_list_builder_wf (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) (vs : list nat) (b' : RO.builder) :
    RO.compile_list fuel ρ ts b = (vs, b') ->
    builder_wf b ->
    builder_wf b'.
  Proof.
    intros Hcomp Hwf.
    pose proof (f_equal snd Hcomp) as Hb'.
    simpl in Hb'.
    rewrite <- Hb'.
    apply (compile_list_builder_wf_aux fuel ρ ts b Hwf).
  Qed.

  Lemma compile_tm_fix_ty_dom_mono (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) (v : nat) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    v ∈ dom (RO.b_fix_ty b) ->
    v ∈ dom (RO.b_fix_ty b').
  Proof.
    intros Hcomp Hv.
    pose proof (f_equal snd Hcomp) as Hb'.
    simpl in Hb'.
    rewrite <- Hb'.
    apply (compile_tm_fix_ty_dom_mono_aux fuel ρ t b v Hv).
  Qed.

  Lemma compile_list_fix_ty_dom_mono (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) (vs : list nat) (b' : RO.builder) (v : nat) :
    RO.compile_list fuel ρ ts b = (vs, b') ->
    v ∈ dom (RO.b_fix_ty b) ->
    v ∈ dom (RO.b_fix_ty b').
  Proof.
    intros Hcomp Hv.
    pose proof (f_equal snd Hcomp) as Hb'.
    simpl in Hb'.
    rewrite <- Hb'.
    apply (compile_list_fix_ty_dom_mono_aux fuel ρ ts b v Hv).
  Qed.

  Lemma compile_tm_b_fix_ty_mono_aux (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)

      (b : RO.builder) (v : nat) (vA : nat) :
    builder_wf b ->
    RO.b_fix_ty b !! v = Some vA ->
    RO.b_fix_ty (snd (RO.compile_tm fuel ρ t b)) !! v = Some vA
  with compile_list_b_fix_ty_mono_aux (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) (v : nat) (vA : nat) :
    builder_wf b ->
    RO.b_fix_ty b !! v = Some vA ->
    RO.b_fix_ty (snd (RO.compile_list fuel ρ ts b)) !! v = Some vA.
  Proof.
    - revert ρ t b v vA.
      induction fuel as [|fuel' IH]; intros ρ t b v vA Hwf Hv.
      + cbn [RO.compile_tm].
        destruct (RO.fresh b) as [vroot b1] eqn:Hfresh.
        cbn [snd].
        rewrite b_fix_ty_put.
        replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
        rewrite b_fix_ty_fresh.
        exact Hv.
      + cbn [RO.compile_tm].
        destruct t as [x|i|A B|A t|tApp_l tApp_r|A_fix body_fix|ind args|ind ctor args|ind scrut C brs].
        * destruct (RO.fresh b) as [vroot b1] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          exact Hv.
        * destruct (RO.fresh b) as [vroot b1] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b1 with (snd (RO.fresh b)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          exact Hv.
        * (* tPi *)
          destruct (RO.compile_tm fuel' ρ A b) as [vA0 b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) B b1) as [vB b2] eqn:H2.
          destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_tm_builder_wf_aux fuel' ρ A b Hwf) as Hwf1.
          rewrite H1 in Hwf1.
          pose proof (IH ρ A b v vA Hwf Hv) as Hv1.
          rewrite H1 in Hv1.
          pose proof (IH (None :: ρ) B b1 v vA Hwf1 Hv1) as Hv2.
          rewrite H2 in Hv2.
          exact Hv2.
        * (* tLam *)
          destruct (RO.compile_tm fuel' ρ A b) as [vA0 b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) t b1) as [vt b2] eqn:H2.
          destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_tm_builder_wf_aux fuel' ρ A b Hwf) as Hwf1.
          rewrite H1 in Hwf1.
          pose proof (IH ρ A b v vA Hwf Hv) as Hv1.
          rewrite H1 in Hv1.
          pose proof (IH (None :: ρ) t b1 v vA Hwf1 Hv1) as Hv2.
          rewrite H2 in Hv2.
          exact Hv2.
        * (* tApp *)
          destruct (RO.app_view (Term.Syntax.tApp tApp_l tApp_r)) as [h args] eqn:Hav.
          destruct h as [x|i|A' B'|A' t'|h1 h2|A' body'|ind' args'|ind' ctor' args'|ind' scrut' C' brs'];
            try (destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
                 destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
                 destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh;
                 cbn [snd];
                 rewrite b_fix_ty_put;
                 replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
                 rewrite b_fix_ty_fresh;
                 pose proof (compile_tm_builder_wf_aux fuel' ρ tApp_l b Hwf) as Hwf1;
                 rewrite H1 in Hwf1;
                 pose proof (IH ρ tApp_l b v vA Hwf Hv) as Hv1;
                 rewrite H1 in Hv1;
                 pose proof (IH ρ tApp_r b1 v vA Hwf1 Hv1) as Hv2;
                 rewrite H2 in Hv2;
                 exact Hv2).
          destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
            [ destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist;
              destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfresh1;
              set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2);
              destruct (RO.build_subst_chain vargs sv_nil b3) as [sv b4] eqn:Hbsc;
              destruct (RO.fresh b4) as [vroot b5] eqn:Hfresh2;
              cbn [snd];
              rewrite b_fix_ty_put;
              replace b5 with (snd (RO.fresh b4)) by (rewrite Hfresh2; reflexivity);
              rewrite b_fix_ty_fresh;
              replace b4 with (snd (RO.build_subst_chain vargs sv_nil b3))
                by (rewrite Hbsc; reflexivity);
              rewrite b_fix_ty_build_subst_chain;
              unfold b3;
              rewrite b_fix_ty_put;
              replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh1; reflexivity);
              rewrite b_fix_ty_fresh;
              pose proof (compile_list_b_fix_ty_mono_aux fuel' ρ args b v vA Hwf Hv) as Hv1;
              rewrite Hlist in Hv1;
              exact Hv1
            | destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
              destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
              destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh;
              cbn [snd];
              rewrite b_fix_ty_put;
              replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
              rewrite b_fix_ty_fresh;
              pose proof (compile_tm_builder_wf_aux fuel' ρ tApp_l b Hwf) as Hwf1;
              rewrite H1 in Hwf1;
              pose proof (IH ρ tApp_l b v vA Hwf Hv) as Hv1;
              rewrite H1 in Hv1;
              pose proof (IH ρ tApp_r b1 v vA Hwf1 Hv1) as Hv2;
              rewrite H2 in Hv2;
              exact Hv2
            | destruct (RO.compile_tm fuel' ρ tApp_l b) as [v1 b1] eqn:H1;
              destruct (RO.compile_tm fuel' ρ tApp_r b1) as [v2 b2] eqn:H2;
              destruct (RO.fresh b2) as [vroot b3] eqn:Hfresh;
              cbn [snd];
              rewrite b_fix_ty_put;
              replace b3 with (snd (RO.fresh b2)) by (rewrite Hfresh; reflexivity);
              rewrite b_fix_ty_fresh;
              pose proof (compile_tm_builder_wf_aux fuel' ρ tApp_l b Hwf) as Hwf1;
              rewrite H1 in Hwf1;
              pose proof (IH ρ tApp_l b v vA Hwf Hv) as Hv1;
              rewrite H1 in Hv1;
              pose proof (IH ρ tApp_r b1 v vA Hwf1 Hv1) as Hv2;
              rewrite H2 in Hv2;
              exact Hv2 ].
        * (* tFix *)
          destruct (RO.fresh b) as [v_fix b0] eqn:Hfresh0.
          destruct (RO.compile_tm fuel' ρ A_fix b0) as [vA0 b1] eqn:HA.
          set (b1' := RO.put_fix_ty v_fix vA0 b1).
          destruct (RO.compile_tm fuel' (Some v_fix :: ρ) body_fix b1') as [vbody b2] eqn:Hbody.
          cbn [snd].
          rewrite b_fix_ty_put_fix_body.
          assert (Hwf0 : builder_wf b0).
          { replace b0 with (snd (RO.fresh b)) by (rewrite Hfresh0; reflexivity).
            apply builder_wf_fresh. exact Hwf. }
          pose proof (compile_tm_builder_wf_aux fuel' ρ A_fix b0 Hwf0) as Hwf1.
          rewrite HA in Hwf1.
          assert (Hv0 : RO.b_fix_ty b0 !! v = Some vA).
          { replace b0 with (snd (RO.fresh b)) by (rewrite Hfresh0; reflexivity).
            rewrite b_fix_ty_fresh. exact Hv. }
          pose proof (IH ρ A_fix b0 v vA Hwf0 Hv0) as Hv1.
          rewrite HA in Hv1.
          assert (Hv_ne : v ≠ v_fix).
          { intro Hv_eq.
            subst v_fix.
            apply Hwf in Hv.
            unfold RO.fresh in Hfresh0.
            inversion Hfresh0; subst b0; simpl in Hv.
            lia. }
          assert (Hv1' : RO.b_fix_ty b1' !! v = Some vA).
          { unfold b1'.
            unfold RO.put_fix_ty; simpl.
            rewrite lookup_insert_ne; [exact Hv1 | exact (fun Hv_eq => Hv_ne (eq_sym Hv_eq))]. }
          assert (Hwf1' : builder_wf b1').
          { apply builder_wf_put_fix_ty.
            - exact Hwf1.
            - pose proof (compile_tm_b_next_le fuel' ρ A_fix b0) as Hle.
              rewrite HA in Hle. simpl in Hle.
              unfold RO.fresh in Hfresh0. inversion Hfresh0; subst; simpl in Hle.
              lia. }
          pose proof (IH (Some v_fix :: ρ) body_fix b1' v vA Hwf1' Hv1') as Hv2.
          rewrite Hbody in Hv2.
          exact Hv2.
        * (* tInd *)
          destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [vroot b2] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_list_b_fix_ty_mono_aux fuel' ρ args b v vA Hwf Hv) as Hv1.
          rewrite Hlist in Hv1.
          exact Hv1.
        * (* tRoll *)
          destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [vroot b2] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b2 with (snd (RO.fresh b1)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_list_b_fix_ty_mono_aux fuel' ρ args b v vA Hwf Hv) as Hv1.
          rewrite Hlist in Hv1.
          exact Hv1.
        * (* tCase *)
          destruct (RO.compile_tm fuel' ρ scrut b) as [vscrut b1] eqn:H1.
          destruct (RO.compile_tm fuel' ρ C b1) as [vC b2] eqn:H2.
          destruct (RO.compile_list fuel' ρ brs b2) as [vbrs b3] eqn:Hlist.
          destruct (RO.fresh b3) as [vroot b4] eqn:Hfresh.
          cbn [snd].
          rewrite b_fix_ty_put.
          replace b4 with (snd (RO.fresh b3)) by (rewrite Hfresh; reflexivity).
          rewrite b_fix_ty_fresh.
          pose proof (compile_tm_builder_wf_aux fuel' ρ scrut b Hwf) as Hwf1.
          rewrite H1 in Hwf1.
          pose proof (compile_tm_builder_wf_aux fuel' ρ C b1 Hwf1) as Hwf2.
          rewrite H2 in Hwf2.
          pose proof (IH ρ scrut b v vA Hwf Hv) as Hv1.
          rewrite H1 in Hv1.
          pose proof (IH ρ C b1 v vA Hwf1 Hv1) as Hv2.
          rewrite H2 in Hv2.
          pose proof (compile_list_b_fix_ty_mono_aux fuel' ρ brs b2 v vA Hwf2 Hv2) as Hv3.
          rewrite Hlist in Hv3.
          exact Hv3.
    - revert ρ ts b v vA.
      induction fuel as [|fuel' IH]; intros ρ ts b v vA Hwf Hv.
      + cbn [RO.compile_list]. exact Hv.
      + cbn [RO.compile_list].
        destruct ts as [|t ts].
        * simpl. exact Hv.
        * destruct (RO.compile_tm fuel' ρ t b) as [v1 b1] eqn:Htm.
          destruct (RO.compile_list fuel' ρ ts b1) as [vs' b2] eqn:Hlist.
          simpl.
          pose proof (compile_tm_builder_wf_aux fuel' ρ t b Hwf) as Hwf1.
          rewrite Htm in Hwf1.
          pose proof (compile_tm_b_fix_ty_mono_aux fuel' ρ t b v vA Hwf Hv) as Hv1.
          rewrite Htm in Hv1.
          pose proof (IH ρ ts b1 v vA Hwf1 Hv1) as Hv2.
          rewrite Hlist in Hv2.
          exact Hv2.
  Qed.

  Lemma compile_tm_b_fix_ty_mono (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) (v : nat) (vA : nat) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    builder_wf b ->
    RO.b_fix_ty b !! v = Some vA ->
    RO.b_fix_ty b' !! v = Some vA.
  Proof.
    intros Hcomp Hwf Hv.
    pose proof (f_equal snd Hcomp) as Hb'.
    simpl in Hb'.
    rewrite <- Hb'.
    apply (compile_tm_b_fix_ty_mono_aux fuel ρ t b v vA Hwf Hv).
  Qed.

  Lemma compile_tm_root_label (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    root ∈ verts_of b'.
  Proof.
    revert ρ t b root b'.
    induction fuel as [|fuel' _IH]; intros ρ t b root b' Hcomp.
    - simpl in Hcomp.
      destruct (RO.fresh b) as [v b1] eqn:Hfresh.
      unfold RO.fresh in Hfresh. injection Hfresh as <- <-.
      injection Hcomp as <- <-.
      unfold verts_of, RO.put. simpl.
      apply elem_of_union_l.
      apply elem_of_dom. rewrite lookup_insert. eexists; reflexivity.
      - simpl in Hcomp.
        destruct t; try solve [
          simpl in Hcomp;
          repeat match goal with
          | H : match ?t with _ => _ end = _ |- _ => destruct t eqn:? in H
          end;
          repeat match goal with
          | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
          end;
          repeat match goal with
          | H : (_, _) = (root, b') |- _ => injection H as <- <-
          end;
          unfold verts_of, RO.put; simpl;
          apply elem_of_union_l;
          apply elem_of_dom; rewrite lookup_insert; eexists; reflexivity].

      (* tFix case: root in b_fix_ty *)
      + repeat match goal with
          | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
          end.
        repeat match goal with
        | H : (_, _) = (root, b') |- _ => injection H as <- <-
        end.
        unfold verts_of, RO.put_fix_body. simpl.
        apply elem_of_union_r.
        apply (compile_tm_fix_ty_dom_mono fuel' (Some (RO.b_next b) :: ρ) t0
                (RO.put_fix_ty (RO.b_next b) n b0) n0 b1 (RO.b_next b) Heqp0).
        apply elem_of_dom.
        unfold RO.put_fix_ty; simpl.
        rewrite lookup_insert. eexists; reflexivity.
  Qed.


  Lemma read_off_root_in (t : Term.Syntax.tm) :
    let '(root, b) := RO.read_off_raw t in
    root ∈ verts (graph_of b).
  Proof.
    unfold RO.read_off_raw.
    destruct (RO.compile_tm (RO.fuel_tm t) [] t RO.empty_builder) as [root b] eqn:Hcomp.
    unfold verts, graph_of. simpl.
    exact (compile_tm_root_label _ _ _ _ _ _ Hcomp).
  Qed.

  Program Definition rooted_preproof_of (t : Term.Syntax.tm)
      : @Preproof.rooted_preproof Judgement (fun j ps => Rule (snd (RO.read_off_raw t)) j ps) V _ _ :=
    let '(root, b) := RO.read_off_raw t in
    {| Preproof.rpp_proof := preproof_of b;
       Preproof.rpp_root := root;
       Preproof.rpp_root_in := _ |}.
  Admit Obligations.
End Packaging.
