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

  Lemma build_subst_chain_b_next_le (us : list nat) (sv_tail : nat) (b : RO.builder) :
    RO.b_next b ≤ RO.b_next (snd (RO.build_subst_chain us sv_tail b)).
  Proof.
    induction us as [|u us IH].
    - simpl. lia.
    - simpl.
      destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hchain.
      destruct (RO.fresh b1) as [sv_head b2] eqn:Hfresh.
      unfold RO.fresh in Hfresh. inversion Hfresh; subst; simpl.
      pose proof IH as Hle.
      replace (snd (RO.build_subst_chain us sv_tail b)) with b1 in Hle
        by (rewrite Hchain; reflexivity).
      simpl in Hle.
      lia.
  Qed.

  (** b_next monotonicity for compile_tm and compile_list. *)
  Lemma compile_tm_b_next_le (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) :
    RO.b_next b ≤ RO.b_next (snd (RO.compile_tm fuel ρ t b))
  with compile_list_b_next_le (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) :
    RO.b_next b ≤ RO.b_next (snd (RO.compile_list fuel ρ ts b)).
  Admitted.

  (** compile_tm preserves builder_wf. *)
  Lemma compile_tm_builder_wf (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    builder_wf b ->
    builder_wf b'
  with compile_list_builder_wf (fuel : nat) (ρ : RO.back_env) (ts : list Term.Syntax.tm)
      (b : RO.builder) (vs : list nat) (b' : RO.builder) :
    RO.compile_list fuel ρ ts b = (vs, b') ->
    builder_wf b ->
    builder_wf b'.
  Proof.
    - revert ρ t b root b'.
      induction fuel as [|fuel' IH]; intros ρ t b root b' Hcomp Hwf.
      + simpl in Hcomp.
        destruct (RO.fresh b) as [v b1] eqn:Hfresh.
        injection Hcomp as _ <-.
        apply builder_wf_put. apply builder_wf_fresh. exact Hwf.
      + simpl in Hcomp.
        destruct t.
        * destruct (RO.fresh b) as [v b1] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put. apply builder_wf_fresh. exact Hwf.
        * destruct (RO.fresh b) as [v b1] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put. apply builder_wf_fresh. exact Hwf.
        * (* tPi *)
          destruct (RO.compile_tm fuel' ρ t1 b) as [vA b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) t2 b1) as [vB b2] eqn:H2.
          destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put.
          apply builder_wf_fresh.
          apply (IH (None :: ρ) t2 b1 vB b2 H2).
          apply (IH ρ t1 b vA b1 H1). exact Hwf.
        * (* tLam *)
          destruct (RO.compile_tm fuel' ρ t1 b) as [vA b1] eqn:H1.
          destruct (RO.compile_tm fuel' (None :: ρ) t2 b1) as [vt b2] eqn:H2.
          destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put.
          apply builder_wf_fresh.
          apply (IH (None :: ρ) t2 b1 vt b2 H2).
          apply (IH ρ t1 b vA b1 H1). exact Hwf.
        * (* tApp *)
          destruct (RO.app_view (Term.Syntax.tApp t1 t2)) as [h args] eqn:Hav.
          destruct h.
          -- destruct (nth_error ρ n) as [[target|]|] eqn:Hnth.
             ++ destruct (RO.compile_list fuel' ρ args b) as [vargs b1] eqn:Hlist.
                destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfresh1.
                destruct (RO.build_subst_chain vargs sv_nil (RO.put sv_nil (RO.nSubstNil 0) [] b2))
                  as [sv b4] eqn:Hbsc.
                destruct (RO.fresh b4) as [v b5] eqn:Hfresh2.
                injection Hcomp as _ <-.
                apply builder_wf_put.
                apply builder_wf_fresh.
                apply builder_wf_put.
                apply builder_wf_fresh.
                apply (compile_list_builder_wf fuel' ρ args b vargs b1 Hlist Hwf).
             ++ destruct (RO.compile_tm fuel' ρ t1 b) as [v1 b1] eqn:H1.
                destruct (RO.compile_tm fuel' ρ t2 b1) as [v2 b2] eqn:H2.
                destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
                injection Hcomp as _ <-.
                apply builder_wf_put.
                apply builder_wf_fresh.
                apply (IH ρ t2 b1 v2 b2 H2).
                apply (IH ρ t1 b v1 b1 H1). exact Hwf.
             ++ destruct (RO.compile_tm fuel' ρ t1 b) as [v1 b1] eqn:H1.
                destruct (RO.compile_tm fuel' ρ t2 b1) as [v2 b2] eqn:H2.
                destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
                injection Hcomp as _ <-.
                apply builder_wf_put.
                apply builder_wf_fresh.
                apply (IH ρ t2 b1 v2 b2 H2).
                apply (IH ρ t1 b v1 b1 H1). exact Hwf.
          -- destruct (RO.compile_tm fuel' ρ t1 b) as [v1 b1] eqn:H1.
             destruct (RO.compile_tm fuel' ρ t2 b1) as [v2 b2] eqn:H2.
             destruct (RO.fresh b2) as [v b3] eqn:Hfresh.
             injection Hcomp as _ <-.
             apply builder_wf_put.
             apply builder_wf_fresh.
             apply (IH ρ t2 b1 v2 b2 H2).
             apply (IH ρ t1 b v1 b1 H1). exact Hwf.
        * (* tFix *)
          destruct (RO.fresh b) as [v_fix b0] eqn:Hfresh0.
          destruct (RO.compile_tm fuel' ρ t1 b0) as [vA b1] eqn:HA.
          destruct (RO.compile_tm fuel' (Some (RO.b_next b) :: ρ) t2
                      (RO.put_fix_ty (RO.b_next b) vA b1)) as [vbody b2] eqn:Hbody.
          injection Hcomp as _ <-.
          apply builder_wf_put_fix_body.
          apply (IH (Some (RO.b_next b) :: ρ) t2 (RO.put_fix_ty (RO.b_next b) vA b1) vbody b2 Hbody).
          apply builder_wf_put_fix_ty.
          + (* builder_wf b1 *)
            apply (IH ρ t1 b0 vA b1 HA).
            apply builder_wf_fresh. exact Hwf.
          + (* v_fix < b_next b1 *)
            pose proof (compile_tm_b_next_le fuel' ρ t1 b0) as Hle.
            rewrite HA in Hle. simpl in Hle.
            unfold RO.fresh in Hfresh0. inversion Hfresh0; subst; simpl in Hle.
            lia.
        * (* tInd *)
          destruct (RO.compile_list fuel' ρ l b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [v b2] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put.
          apply builder_wf_fresh.
          apply (compile_list_builder_wf fuel' ρ l b vargs b1 Hlist Hwf).
        * (* tRoll *)
          destruct (RO.compile_list fuel' ρ l b) as [vargs b1] eqn:Hlist.
          destruct (RO.fresh b1) as [v b2] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put.
          apply builder_wf_fresh.
          apply (compile_list_builder_wf fuel' ρ l b vargs b1 Hlist Hwf).
        * (* tCase *)
          destruct (RO.compile_tm fuel' ρ t1 b) as [vscrut b1] eqn:H1.
          destruct (RO.compile_tm fuel' ρ t2 b1) as [vC b2] eqn:H2.
          destruct (RO.compile_list fuel' ρ l b2) as [vbrs b3] eqn:Hlist.
          destruct (RO.fresh b3) as [v b4] eqn:Hfresh.
          injection Hcomp as _ <-.
          apply builder_wf_put.
          apply builder_wf_fresh.
          apply (compile_list_builder_wf fuel' ρ l b2 vbrs b3 Hlist).
          apply (IH ρ t2 b1 vC b2 H2).
          apply (IH ρ t1 b vscrut b1 H1). exact Hwf.
    - revert ρ ts b vs b'.
      induction fuel as [|fuel' IH]; intros ρ ts b vs b' Hcomp Hwf.
      + simpl in Hcomp. inversion Hcomp; subst. exact Hwf.
      + simpl in Hcomp.
        destruct ts as [|t ts].
        * inversion Hcomp; subst. exact Hwf.
        * destruct (RO.compile_tm fuel' ρ t b) as [v b1] eqn:Htm.
          destruct (RO.compile_list fuel' ρ ts b1) as [vs' b2] eqn:Hlist.
          inversion Hcomp; subst.
          apply (IH ρ ts b1 vs' b2 Hlist).
          apply (compile_tm_builder_wf fuel' ρ t b v b1 Htm Hwf).
  Qed.

  (** compile_tm preserves existing b_fix_ty entries (monotonicity).
      Requires builder_wf as a precondition to handle the tFix case. *)
  Lemma compile_tm_b_fix_ty_mono (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) (v : nat) (vA : nat) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    builder_wf b ->
    RO.b_fix_ty b !! v = Some vA ->
    RO.b_fix_ty b' !! v = Some vA.
  Proof.
    revert ρ t b root b'.
    induction fuel as [|fuel' IH]; intros ρ t b root b' Hcomp Hwf Hv.
    - simpl in Hcomp.
      destruct (RO.fresh b) as [? b1] eqn:Hfresh.
      unfold RO.fresh in Hfresh. injection Hfresh as _ <-.
      injection Hcomp as _ <-.
      unfold RO.put; simpl. exact Hv.
    - simpl in Hcomp.
      destruct t; try (
        repeat match goal with
        | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
        end;
        match goal with
        | H : (_, _) = (root, b') |- _ => injection H as _ <-
        end;
        unfold RO.put, RO.put_fix_body, RO.build_subst_chain; simpl; exact Hv).
      (* tFix case: put_fix_ty inserts a fresh vertex; existing v is preserved *)
      + destruct (RO.fresh b) as [v_fix b0] eqn:Hfresh0.
        unfold RO.fresh in Hfresh0. injection Hfresh0 as <- <-.
        destruct (RO.compile_tm fuel' ρ t1 b0) as [vA0 b1] eqn:HA.
        destruct (RO.compile_tm fuel' (Some (RO.b_next b) :: ρ) t2
                    (RO.put_fix_ty (RO.b_next b) vA0 b1)) as [vbody b2] eqn:Hbody.
        injection Hcomp as _ <-.
        unfold RO.put_fix_body; simpl.
        assert (Hv1 : RO.b_fix_ty b1 !! v = Some vA).
        { apply (IH ρ t1 b0 vA0 b1 v vA HA).
          - apply builder_wf_fresh. exact Hwf.
          - simpl. exact Hv. }
        assert (Hv_ne : v ≠ RO.b_next b).
        { intro Heq. rewrite Heq in Hv. apply Hwf in Hv. lia. }
        assert (Hv1' : RO.b_fix_ty (RO.put_fix_ty (RO.b_next b) vA0 b1) !! v = Some vA).
        { unfold RO.put_fix_ty; simpl.
          rewrite lookup_insert_ne; [exact Hv1 | exact Hv_ne]. }
        apply (IH (Some (RO.b_next b) :: ρ) t2
                  (RO.put_fix_ty (RO.b_next b) vA0 b1) vbody b2 v vA Hbody).
        - apply builder_wf_put_fix_ty.
          + apply (compile_tm_builder_wf fuel' ρ t1 b0 vA0 b1 HA).
            apply builder_wf_fresh. exact Hwf.
          + pose proof (compile_tm_b_next_le fuel' ρ t1 b0) as Hle.
            rewrite HA in Hle. simpl in Hle.
            unfold RO.fresh in Hfresh0. inversion Hfresh0; subst; simpl in Hle.
            lia.
        - exact Hv1'.
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
      apply elem_of_dom. rewrite lookup_insert_eq. eexists; reflexivity.
    - simpl in Hcomp.
      destruct t; try solve [
        repeat match goal with
        | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
        end;
        match goal with
        | H : (_, _) = (root, b') |- _ => injection H as <- <-
        end;
        unfold verts_of, RO.put; simpl;
        apply elem_of_union_l;
        apply elem_of_dom; rewrite lookup_insert_eq; eexists; reflexivity].
      (* tFix case: root in b_fix_ty *)
      + repeat match goal with
          | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
          end.
        match goal with
        | H : (_, _) = (root, b') |- _ => injection H as <- <-
        end.
        unfold verts_of, RO.put_fix_body. simpl.
        apply elem_of_union_r.
        apply elem_of_dom.
        apply (compile_tm_b_fix_ty_mono fuel' ρ body
                (RO.put_fix_ty (RO.b_next b) n0 b1) n1 b0 (RO.b_next b) n0).
        * exact H1.
        * (* builder_wf for put_fix_ty *)
          apply builder_wf_put_fix_ty.
          -- (* builder_wf b1 *)
             intros u vA Hu.
             apply (compile_tm_b_fix_ty_mono fuel' ρ A b0 n0 b1 u vA H0).
             ++ intros u' vA' Hu'.
                unfold RO.fresh in Hfresh. inversion Hfresh; subst; simpl. lia.
             ++ exact Hu.
          -- (* v_fix < b_next b1 *)
             pose proof (compile_tm_b_next_le fuel' ρ A b0) as Hle.
             rewrite H0 in Hle. simpl in Hle.
             unfold RO.fresh in Hfresh. inversion Hfresh; subst; simpl in Hle.
             lia.
        * (* lookup_insert_eq for v_fix *)
          unfold RO.put_fix_ty. simpl. rewrite lookup_insert_eq. reflexivity.
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
