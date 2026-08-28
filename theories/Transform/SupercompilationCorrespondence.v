From Stdlib Require Import List Arith Lia Utf8 Relations Relation_Operators.
From stdpp Require Import prelude countable gmap fin_sets.
From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Progress Require Import PatternUnification.
From Cyclic.Transform Require Import ReadOff ReadOffDrivingPreproof Supercompile SupercompileTraceCheckSound SequentDrivingRules SequentObservationRules CyclicTraceConditionObsTree CyclicTraceConditionBudget.
From Cyclic.Semantics Require Cbn.
From Cyclic.CyclicProof Require Import Ranked.
From Cyclic.Equiv Require Import CIU CIUJudgement.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module RDP := ReadOffDrivingPreproof.
Module SC := Supercompile.
Module SDR := SequentDrivingRules.
Module SOR := SequentObservationRules.
Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module PU := PatternUnification.
Module RDPDefs := ReadOffDrivingPreproofDefs.
Module STC := SupercompileTraceCheckSound.
Module CTB := CyclicTraceConditionBudget.

(** Configurations-as-vertices view of a [cfg_builder]: labels, local rule, and
    vertex set, used to build the trace-level cyclic proof. *)
Definition sc_pp_label (scb : SC.cfg_builder) (v : nat) : config :=
  default (C.jTy [] (tVar 0) (tSort 0)) (SC.lookup_label scb v).

Definition sc_rule (Σenv : Ty.env) : config -> list config -> Prop :=
  SDR.drive_rule Σenv.

Definition sc_verts (scb : SC.cfg_builder) : gset nat :=
  dom scb.(SC.cb_label).

(** Correspondence: Supercompilation ≅ Cyclic Sequent Proof Search

    This file proves that supercompilation moves correspond exactly to
    operations on cyclic sequent proof graphs. This establishes the
    paper's core claim: "supercompilation IS cyclic proof search".
    
    Key correspondences:
    1. drive_cbn_once ↔ async driving edge (local rule)
    2. split_case_var ↔ synchronous split edge (choice point)
    3. fold/memo lookup ↔ backlink insertion (cycle formation)
    4. generalize ↔ generalisation edge (future work)
    
    Structure of the proof:
    - Define a bisimulation between cfg_builder (SC state) and rooted_preproof
    - Show each SC operation preserves the bisimulation
    - Conclude: SC success ⟹ valid cyclic proof
*)

Section Correspondence.

  (** * Bisimulation Overview
  
      The correspondence between supercompilation and cyclic proof search is
      established via a bisimulation between two graph structures:
      
      1. **SC side (cfg_builder)**: Supercompilation configuration graph
         - Vertices: Natural numbers
         - Labels: `cb_label : gmap nat config` (configurations = judgements)
         - Edges: `cb_succ : gmap nat (list nat)` (successor vertices)
         - Additional data: `cb_inst`, `cb_holes` (for generalization)
      
      2. **Proof side (rooted_preproof)**: Cyclic sequent proof graph
         - Vertices: Natural numbers (same domain)
         - Labels: Sequent judgements (RDPDefs.jDrive, jObs, jSub)
         - Edges: `RDPDefs.succ_of : builder -> nat -> list nat`
         - Built from `ReadOff.read_off_raw : tm -> (nat * builder)`
      
      The bisimulation invariants ensure:
      - Same vertices (domains equal)
      - Labels correspond (SC config = sequent with extracted term)
      - Edges correspond (same successors)
      - Local validity (each vertex satisfies its sequent rule)
  *)

  (** ** Helper lemmas for working with bisimulation *)
  
  (** Vertex membership in SC graph domain *)
  Lemma vertex_in_sc_dom : forall scb v cfg,
    scb.(SC.cb_label) !! v = Some cfg ->
    v ∈ dom scb.(SC.cb_label).
  Proof.
    intros scb v cfg Hlabel.
    apply elem_of_dom.
    exists cfg. exact Hlabel.
  Qed.

  (** Vertex membership in proof graph *)
  Lemma vertex_in_proof_graph : forall b v lbl,
    RO.b_label b !! v = Some lbl ->
    v ∈ dom (RO.b_label b).
  Proof.
    intros b v lbl Hlabel.
    apply elem_of_dom.
    exists lbl. exact Hlabel.
  Qed.

  (** Successor lookup some implies successors exist *)
  Lemma succ_lookup_some : forall scb v succs,
    scb.(SC.cb_succ) !! v = Some succs ->
    v ∈ dom scb.(SC.cb_succ).
  Proof.
    intros scb v succs Hsucc.
    apply elem_of_dom.
    exists succs. exact Hsucc.
  Qed.

  (** Bisimulation relation: SC state ≈ cyclic proof state
  
      A configuration graph (cfg_builder) corresponds to a rooted preproof when:
      1. Vertices match: same domain
      2. Labels match: SC config = extracted term from proof vertex
      3. Edges match: SC successors = proof graph successors
      4. Local validity: each proof vertex satisfies its sequent rule
  *)
  Definition sc_rooted_preproof (Σenv : Ty.env) (t : tm) : Type :=
    @Preproof.rooted_preproof judgement (fun _ _ => True) nat _ _.

  Record bisim (Σenv : Ty.env) (fuel : nat)
      (scb : SC.cfg_builder) (t : tm) (proof : sc_rooted_preproof Σenv t) : Prop := {
    (** Vertex correspondence *)
    bis_verts_eq :
      dom scb.(SC.cb_label) = dom (RO.b_label (snd (RO.read_off_raw t)));

    (** Label correspondence: SC configs match extracted terms *)
    bis_label_match : forall v cfg,
      scb.(SC.cb_label) !! v = Some cfg ->
      exists t0 A Γ,
        cfg = C.jTy Γ t0 A /\
        RDPDefs.pp_label fuel (snd (RO.read_off_raw t)) v = RDPDefs.jDrive cfg;

    (** Edge correspondence: successors match *)
    bis_succ_match : forall v succs,
      scb.(SC.cb_succ) !! v = Some succs ->
      RDPDefs.succ_of (snd (RO.read_off_raw t)) v = succs;

    (** Local validity: each vertex satisfies its rule *)
    bis_local_valid : forall v,
      v ∈ dom scb.(SC.cb_label) ->
      RDPDefs.rule Σenv (snd (RO.read_off_raw t))
        (RDPDefs.pp_label fuel (snd (RO.read_off_raw t)) v)
        (map (RDPDefs.pp_label fuel (snd (RO.read_off_raw t)))
             (RDPDefs.succ_of (snd (RO.read_off_raw t)) v));
  }.

  (** ** Derived bisimulation lemmas
  
      These lemmas extract useful facts from the bisimulation relation.
  *)

  (** Vertex correspondence: if v is in SC graph, it's in proof graph *)
  Lemma bisim_vertex_in_proof :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v,
      bisim Σenv fuel scb t proof ->
      v ∈ dom (SC.cb_label scb) ->
      v ∈ dom (RO.b_label (snd (RO.read_off_raw t))).
  Proof.
    intros Σenv fuel scb t proof v Hbis Hv_sc.
    destruct Hbis as [Hverts _ _ _].
    rewrite <- Hverts. exact Hv_sc.
  Qed.

  (** Vertex correspondence: if v is in proof graph, it's in SC graph *)
  Lemma bisim_vertex_in_sc :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v,
      bisim Σenv fuel scb t proof ->
      v ∈ dom (RO.b_label (snd (RO.read_off_raw t))) ->
      v ∈ dom (SC.cb_label scb).
  Proof.
    intros Σenv fuel scb t proof v Hbis Hv_proof.
    destruct Hbis as [Hverts _ _ _].
    rewrite Hverts. exact Hv_proof.
  Qed.

  (** Label correspondence: SC label gives proof label *)
  Lemma bisim_label_exists :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v cfg,
      bisim Σenv fuel scb t proof ->
      SC.cb_label scb !! v = Some cfg ->
      RDPDefs.pp_label fuel (snd (RO.read_off_raw t)) v = RDPDefs.jDrive cfg.
  Proof.
    intros Σenv fuel scb t proof v cfg Hbis Hlabel.
    destruct Hbis as [_ Hlabelmatch _ _].
    destruct (Hlabelmatch v cfg Hlabel) as [t0 [A [Γ [_ Hpplabel]]]].
    exact Hpplabel.
  Qed.

  (** Edge correspondence: SC successors give proof successors *)
  Lemma bisim_succ_eq :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v succs,
      bisim Σenv fuel scb t proof ->
      SC.cb_succ scb !! v = Some succs ->
      RDPDefs.succ_of (snd (RO.read_off_raw t)) v = succs.
  Proof.
    intros Σenv fuel scb t proof v succs Hbis Hsucc.
    destruct Hbis as [_ _ Hsuccmatch _].
    apply Hsuccmatch. exact Hsucc.
  Qed.

  (** Local validity for a specific vertex *)
  Lemma bisim_vertex_valid :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v cfg,
      bisim Σenv fuel scb t proof ->
      SC.cb_label scb !! v = Some cfg ->
      RDPDefs.rule Σenv (snd (RO.read_off_raw t))
        (RDPDefs.pp_label fuel (snd (RO.read_off_raw t)) v)
        (map (RDPDefs.pp_label fuel (snd (RO.read_off_raw t)))
             (RDPDefs.succ_of (snd (RO.read_off_raw t)) v)).
  Proof.
    intros Σenv fuel scb t proof v cfg Hbis Hlabel.
    destruct Hbis as [_ _ _ Hvalid].
    apply Hvalid.
    exact (vertex_in_sc_dom scb v cfg Hlabel).
  Qed.

  (** ** Notation for cleaner proofs *)
  
  Local Notation "'builder_of' t" := (snd (RO.read_off_raw t)) (at level 50).
  Local Notation "'root_of' t" := (fst (RO.read_off_raw t)) (at level 50).

  (** ** Soundness of computational driving *)
  Lemma drive_cbn_once_sound' :
    forall t,
      SDR.drive_cbn_onceR t (SC.drive_cbn_once t).
  Proof.
    induction t as [x | i | A IHA B IHB | A IHA body IHbody | t1 IHt1 t2 IHt2 | A IHA body IHbody | I args | I c args | I scrut IHscrut C IHC brs];
      simpl; try constructor.
    - (* tApp *)
      remember (SC.drive_cbn_once t1) as t1' eqn:Ht1'.
      destruct t1' as [x' | i' | A' B' | A' body' | u1 u2 | A' body' | I' args' | I' c' args' | I' s' C' brs'].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + eapply SDR.dc_app_beta; [exact IHt1 | reflexivity].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
      + apply SDR.dc_app_cong; [exact IHt1 | intros A0 b Hb; discriminate].
    - (* tCase *)
      simpl.
      destruct scrut as [x' | i' | A' B' | A' body' | s1 s2 | A' body' | I' args' | I' c' args' | I2 s2 C2 brs2].
      + (* scrut = tVar *)
        cbv zeta.
        destruct (SC.tm_eqb (tVar x') (SC.drive_cbn_once (tVar x'))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tVar x') C brs (SC.drive_cbn_once (tVar x'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tVar x') C brs (SC.drive_cbn_once (tVar x'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tSort *)
        cbv zeta.
        destruct (SC.tm_eqb (tSort i') (SC.drive_cbn_once (tSort i'))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tSort i') C brs (SC.drive_cbn_once (tSort i'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tSort i') C brs (SC.drive_cbn_once (tSort i'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tPi *)
        cbv zeta.
        destruct (SC.tm_eqb (tPi A' B') (SC.drive_cbn_once (tPi A' B'))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tPi A' B') C brs (SC.drive_cbn_once (tPi A' B'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tPi A' B') C brs (SC.drive_cbn_once (tPi A' B'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tLam *)
        cbv zeta.
        destruct (SC.tm_eqb (tLam A' body') (SC.drive_cbn_once (tLam A' body'))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tLam A' body') C brs (SC.drive_cbn_once (tLam A' body'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tLam A' body') C brs (SC.drive_cbn_once (tLam A' body'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tApp *)
        cbv zeta.
        destruct (SC.tm_eqb (tApp s1 s2) (SC.drive_cbn_once (tApp s1 s2))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tApp s1 s2) C brs (SC.drive_cbn_once (tApp s1 s2))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tApp s1 s2) C brs (SC.drive_cbn_once (tApp s1 s2))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tFix *)
        cbv zeta.
        destruct (SC.tm_eqb (tFix A' body') (SC.drive_cbn_once (tFix A' body'))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tFix A' body') C brs (SC.drive_cbn_once (tFix A' body'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tFix A' body') C brs (SC.drive_cbn_once (tFix A' body'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tInd *)
        cbv zeta.
        destruct (SC.tm_eqb (tInd I' args') (SC.drive_cbn_once (tInd I' args'))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tInd I' args') C brs (SC.drive_cbn_once (tInd I' args'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tInd I' args') C brs (SC.drive_cbn_once (tInd I' args'))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
      + (* scrut = tRoll *)
        simpl.
        destruct (Nat.eqb I I') eqn:Heqind.
        * apply Nat.eqb_eq in Heqind. subst I'.
          destruct (branch brs c') eqn:Hbr.
          -- eapply SDR.dc_case_iota.
             ++ reflexivity.
             ++ reflexivity.
             ++ exact Hbr.
          -- eapply SDR.dc_case_roll_no_branch.
             ++ reflexivity.
             ++ reflexivity.
             ++ exact Hbr.
        * apply Nat.eqb_neq in Heqind.
          eapply SDR.dc_case_roll_ind_mismatch.
          -- reflexivity.
          -- exact Heqind.
      + (* scrut = tCase *)
        cbv zeta.
        destruct (SC.tm_eqb (tCase I2 s2 C2 brs2) (SC.drive_cbn_once (tCase I2 s2 C2 brs2))) eqn:Heqb.
        * apply (SDR.dc_case_scrut_stuck I (tCase I2 s2 C2 brs2) C brs (SC.drive_cbn_once (tCase I2 s2 C2 brs2))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- symmetry. apply (PU.tm_eqb_eq _ _ Heqb).
        * apply (SDR.dc_case_scrut_step I (tCase I2 s2 C2 brs2) C brs (SC.drive_cbn_once (tCase I2 s2 C2 brs2))).
          -- intros ind' c args Hc. discriminate.
          -- exact IHscrut.
          -- intro Hc. apply (PU.tm_eqb_neq _ _ Heqb). symmetry. exact Hc.
  Qed.

  Lemma drive_cbn_once_sound :
    forall t u,
      SC.drive_cbn_once t = u ->
      SDR.drive_cbn_onceR t u.
  Proof.
    intros t u Hdrive.
    subst u.
    apply drive_cbn_once_sound'.
  Qed.

  (** Correspondence Theorem 1: drive_cbn_once = async edge
  
      If SC performs a single driving step, the corresponding proof graph
      has a valid drive rule.
      
      Simplified version: we show the rule is valid, not that the edge exists
      in the graph (that requires understanding SC graph construction).
  *)
  
  Theorem drive_cbn_once_gives_drive_rule :
    forall Σenv Γ t A u,
      SC.drive_cbn_once t = u ->
      u <> t ->
      SDR.drive_rule Σenv (C.jTy Γ t A) [C.jTy Γ u A].
  Proof.
    intros Σenv Γ t A u Hdrive Hneq.
    apply SDR.dr_cbn_once.
    - apply drive_cbn_once_sound. exact Hdrive.
    - exact Hneq.
  Qed.

  (** E1: macro driving via [whnf_drive]

      The supercompiler sometimes uses [whnf_drive] as an eager driving macro.
      We expose this as a separate notion of an asynchronous move.
   *)
  Definition whnf_async (t u : tm) : Prop :=
    exists k, k <> 0 /\ u = SC.whnf_drive k t.

  (** E2: [whnf_drive] expands to a chain of one-step driving rules.

      This derives the sequent-calculus view (many async steps) from the
      implementation view (one macro step).
   *)
  Lemma whnf_drive_gives_drive_rule_rtc :
    forall Σenv Γ A k t,
      clos_refl_trans tm
        (fun t1 t2 => SDR.drive_rule Σenv (C.jTy Γ t1 A) [C.jTy Γ t2 A])
        t (SC.whnf_drive k t).
  Proof.
    intros Σenv Γ A k.
    induction k as [|k' IH]; intro t.
    - cbn. apply rt_refl.
    - cbn.
      set (t' := SC.drive_cbn_once t) in *.
      destruct (SC.tm_eqb t t') eqn:Heq.
      + cbn. apply rt_refl.
      + apply PU.tm_eqb_neq in Heq.
        eapply rt_trans.
        * apply rt_step.
          apply (drive_cbn_once_gives_drive_rule Σenv Γ t A t').
          -- unfold t'. reflexivity.
          -- intro Hc. apply Heq. symmetry. exact Hc.
        * exact (IH t').
  Qed.

  (** Correspondence Theorem 1 (graph-level): driving = async edge
  
      When the supercompiler records a single-successor edge [v → w] that is
      justified by a one-step call-by-name drive on the underlying term, the
      read-off proof graph has the same edge, and the successor vertex carries
      the driven configuration label.
  *)
  Theorem drive_corresponds_to_async_edge :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v Γ t0 A u w,
      bisim Σenv fuel scb t proof ->
      scb.(SC.cb_label) !! v = Some (C.jTy Γ t0 A) ->
      SC.drive_cbn_once t0 = u ->
      u <> t0 ->
      scb.(SC.cb_succ) !! v = Some [w] ->
      scb.(SC.cb_label) !! w = Some (C.jTy Γ u A) ->
      w ∈ RDPDefs.succ_of (builder_of t) v /\
      RDPDefs.pp_label fuel (builder_of t) w = RDPDefs.jDrive (C.jTy Γ u A) /\
      SDR.drive_rule Σenv (C.jTy Γ t0 A) [C.jTy Γ u A].
  Proof.
    intros Σenv fuel scb t proof v Γ t0 A u w Hbis Hv Hdrive Hneq Hsucc Hw.
    pose proof (bisim_succ_eq _ _ _ _ _ _ _ Hbis Hsucc) as Hsucc_proof.
    pose proof (bisim_label_exists _ _ _ _ _ _ _ Hbis Hw) as Hw_label.
    split.
    - rewrite Hsucc_proof. set_solver.
    - split.
      + exact Hw_label.
      + apply (drive_cbn_once_gives_drive_rule Σenv Γ t0 A u); assumption.
  Qed.

  (** Correspondence Theorem 2: split_case_var = synchronous choice
  
      As with driving, we first prove the "rule correctness" statement:
      if the supercompiler computes split successors, the corresponding
      sequent split rule is applicable.
  *)

  Theorem split_case_var_gives_drive_rule :
    forall Σenv Γ ind x Cmot brs A succs,
      SC.split_case_var Σenv Γ ind x Cmot brs A = succs ->
      succs <> [] ->
      SDR.drive_rule Σenv (C.jTy Γ (tCase ind (tVar x) Cmot brs) A) succs.
  Proof.
    intros Σenv Γ ind x Cmot brs A succs Hsplits Hne.
    eapply SDR.dr_split_case_var.
    exact Hne.
  Qed.

  (** Correspondence Theorem 2 (graph-level): splitting = synchronous edges
  
      When the supercompiler splits on a neutral case-variable and records
      multiple successor edges [v → w1, v → w2, ...], the read-off proof graph
      has the same edges, each successor carries the corresponding branch
      configuration, and the split satisfies the sequent split rule.
  *)
  Theorem split_corresponds_to_sync_edge :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v Γ ind x Cmot brs A succs ws,
      bisim Σenv fuel scb t proof ->
      scb.(SC.cb_label) !! v = Some (C.jTy Γ (tCase ind (tVar x) Cmot brs) A) ->
      succs = SC.split_case_var Σenv Γ ind x Cmot brs A ->
      succs <> [] ->
      scb.(SC.cb_succ) !! v = Some ws ->
      (forall w cfg, w ∈ ws -> scb.(SC.cb_label) !! w = Some cfg -> 
         w ∈ RDPDefs.succ_of (builder_of t) v /\
         RDPDefs.pp_label fuel (builder_of t) w = RDPDefs.jDrive cfg) /\
      SDR.drive_rule Σenv (C.jTy Γ (tCase ind (tVar x) Cmot brs) A) succs.
  Proof.
    intros Σenv fuel scb t proof v Γ ind x Cmot brs A succs ws 
           Hbis Hv Hsplits Hne Hsucc.
    pose proof (bisim_succ_eq _ _ _ _ _ _ _ Hbis Hsucc) as Hsucc_proof.
    split.
    - intros w cfg Hw_in Hw_label.
      pose proof (bisim_label_exists _ _ _ _ _ _ _ Hbis Hw_label) as Hw_proof_label.
      split.
      + rewrite Hsucc_proof. exact Hw_in.
      + exact Hw_proof_label.
    - apply (split_case_var_gives_drive_rule Σenv Γ ind x Cmot brs A succs).
      + symmetry. exact Hsplits.
      + exact Hne.
  Qed.

  (** Correspondence Theorem 3: memo lookup = fold/backlink
  
      Again we first establish a "rule correctness" statement: if the memo table
      hits, the supercompiler reuses an existing vertex (i.e. performs a fold).

      This is the cfg-graph analogue of forming a backlink in the proof graph.
  *)

  Lemma memo_hit_implies_equal : forall cfg cfg_prev,
    SC.judgement_eqb cfg cfg_prev = true -> cfg = cfg_prev.
  Proof.
    intros cfg cfg_prev H.
    apply SC.judgement_eqb_eq.
    exact H.
  Qed.

  Lemma supercompile_cfg_memo_hit :
    forall fuel Σenv j st v,
      SC.memo_lookup
        (SC.canon_config (SC.norm_config SC.memo_norm_fuel Σenv j))
        st.(SC.sc_memo) = Some v ->
      SC.supercompile_cfg fuel Σenv j st = Some (v, st).
  Proof.
    intros fuel Σenv j st v Hlookup.
    destruct fuel as [|fuel'].
    - cbn [supercompile_cfg]. rewrite Hlookup. reflexivity.
    - cbn [supercompile_cfg]. rewrite Hlookup. reflexivity.
  Qed.

  (** Correspondence Theorem 3 (graph-level): memo hit = backlink/fold
  
      When the supercompiler performs a memo lookup and finds a matching
      configuration at vertex v_prev, creating a backlink edge [v → v_prev],
      the read-off proof graph has the same backlink edge, and the two
      vertices have matching (equivalent) labels.
      
      NOTE: This is a simplified version. A complete statement would also
      show that the backlink satisfies the cyclic proof validity condition
      (the companion v_prev is an ancestor of v in the call tree).
  *)
  Theorem memo_corresponds_to_fold :
    forall Σenv fuel scb t (proof : sc_rooted_preproof Σenv t) v v_prev cfg,
      bisim Σenv fuel scb t proof ->
      scb.(SC.cb_label) !! v = Some cfg ->
      scb.(SC.cb_succ) !! v = Some [v_prev] ->
      scb.(SC.cb_label) !! v_prev = Some cfg ->
      v_prev ∈ RDPDefs.succ_of (builder_of t) v /\
      RDPDefs.pp_label fuel (builder_of t) v = RDPDefs.jDrive cfg /\
      RDPDefs.pp_label fuel (builder_of t) v_prev = RDPDefs.jDrive cfg.
  Proof.
    intros Σenv fuel scb t proof v v_prev cfg Hbis Hv Hsucc Hv_prev.
    pose proof (bisim_succ_eq _ _ _ _ _ _ _ Hbis Hsucc) as Hsucc_proof.
    pose proof (bisim_label_exists _ _ _ _ _ _ _ Hbis Hv) as Hv_label.
    pose proof (bisim_label_exists _ _ _ _ _ _ _ Hbis Hv_prev) as Hv_prev_label.
    split.
    - rewrite Hsucc_proof. set_solver.
    - split; assumption.
Qed.

  (** * Focused Sequent Rule Classification

      Each vertex in the cfg_builder satisfies a specific [drive_rule]
      determined by its successor structure:
      - 0 successors: leaf axiom
      - 1 successor, drive_cbn_once: [dr_cbn_once]
      - 1 successor, memo hit: backlink (handled by fold correspondence)
      - n>1 successors, case-split: [dr_split_case_var]

      The full statement requires the label/successor consistency invariant
      of [supercompile_cfg] (a successor vertex is labelled with the drive
      result of its predecessor).  We factor that out as
      [vertex_drive_rule_holds] below; proving it is an induction on
      [supercompile_cfg] (future work).
  *)
  Definition vertex_drive_rule_holds (Σenv : Ty.env) (scb : SC.cfg_builder) : Prop :=
    forall v cfg succs,
      scb.(SC.cb_label) !! v = Some cfg ->
      scb.(SC.cb_succ) !! v = Some succs ->
      SDR.drive_rule Σenv cfg
        (map (fun w => match scb.(SC.cb_label) !! w with
          | Some cfg' => cfg'
          | None => C.jTy [] (tVar 0) (tSort 0) end) succs).

  Lemma cfg_vertex_drive_rule (Σenv : Ty.env) (scb : SC.cfg_builder)
      (v : nat) (cfg : config) (succs : list nat) :
    vertex_drive_rule_holds Σenv scb ->
    scb.(SC.cb_label) !! v = Some cfg ->
    scb.(SC.cb_succ) !! v = Some succs ->
    SDR.drive_rule Σenv cfg
      (map (fun w => match scb.(SC.cb_label) !! w with
        | Some cfg' => cfg'
        | None => C.jTy [] (tVar 0) (tSort 0) end) succs).
  Proof.
    intros Hinv Hlabel Hsucc.
    exact (Hinv v cfg succs Hlabel Hsucc).
  Qed.

  (** Helper lemmas for the end-to-end proof *)
  
  (** Structural invariant: cfg_builder has well-formed graph structure *)
  
  (** Proof strategy for cfg_builder_well_formed:
  
      The proof would proceed by induction on fuel and case analysis on the
      structure of supercompile_cfg. The key observations are:
      
      1. sc_alloc always adds the new vertex to cb_label before returning
      2. compile_succs recursively calls supercompile_cfg, which allocates
         each successor before adding it
      3. cb_put_succ only adds successors that have been returned by compile_succs
      4. Therefore, by induction, all successors are in dom cb_label
      
      The proof requires careful bookkeeping of vertex freshness and map updates.
      
      Key helper lemmas needed:
      - cb_fresh produces fresh vertices (not in current domain)
      - cb_put_label preserves existing labels
      - cb_put_succ doesn't affect cb_label
      - memo_lookup only returns vertices that exist in memo (hence in cb_label)
  *)
  
  (** Helper: sc_alloc adds the vertex to cb_label *)
  Lemma sc_alloc_adds_label :
    forall j st v st',
      SC.sc_alloc j st = (v, st') ->
      v ∈ dom st'.(SC.sc_builder).(SC.cb_label).
  Proof.
    intros j st v st' Halloc.
    unfold SC.sc_alloc in Halloc.
    destruct (SC.cb_fresh _) as [v' b'] eqn:Hfresh.
    injection Halloc as Hv Hst'. subst.
    simpl.
    unfold SC.cb_put_label. simpl.
    apply elem_of_dom.
    exists j.
    apply lookup_insert.
  Qed.

  (** Domain monotonicity for the supercompiler state.

      Supercompilation only allocates new labelled vertices; it never removes
      entries from [cb_label]. This lemma is used to propagate domain membership
      across the threaded [compile_succs] state.
   *)
  Lemma cb_put_succ_label (v : nat) (s : list nat) (b : SC.cfg_builder) :
    (SC.cb_put_succ v s b).(SC.cb_label) = b.(SC.cb_label).
  Proof. reflexivity. Qed.

  Lemma cb_put_inst_label (v : nat) (σ : list tm) (b : SC.cfg_builder) :
    (SC.cb_put_inst v σ b).(SC.cb_label) = b.(SC.cb_label).
  Proof. reflexivity. Qed.

  Lemma cb_put_holes_label (v : nat) (hs : list tm) (b : SC.cfg_builder) :
    (SC.cb_put_holes v hs b).(SC.cb_label) = b.(SC.cb_label).
  Proof. reflexivity. Qed.

  Lemma cb_fresh_label (b : SC.cfg_builder) :
    (snd (SC.cb_fresh b)).(SC.cb_label) = b.(SC.cb_label).
  Proof. unfold SC.cb_fresh. simpl. reflexivity. Qed.

  Lemma sc_alloc_dom_mono (j : SC.config) (st : SC.sc_state) (v : nat) (st' : SC.sc_state) :
    SC.sc_alloc j st = (v, st') ->
    dom st.(SC.sc_builder).(SC.cb_label) ⊆ dom st'.(SC.sc_builder).(SC.cb_label).
  Proof.
    intros Halloc.
    unfold SC.sc_alloc in Halloc.
    destruct (SC.cb_fresh st.(SC.sc_builder)) as [vf bf] eqn:Hfresh.
    unfold SC.cb_fresh in Hfresh.
    injection Hfresh as Hvf Hbf. subst vf bf.
    injection Halloc as <- <-.
    cbn.
    set_solver.
  Qed.

  (** Helper: compile_succs preserves domain monotonicity, given that each
      individual [supercompile_cfg] call does. *)
  Lemma compile_succs_dom_mono :
    forall fuel Σenv js st ws st',
      (fix compile_succs (js : list SC.config) (st0 : SC.sc_state) :=
         match js with
         | [] => Some ([], st0)
         | j0 :: js0 =>
             match SC.supercompile_cfg fuel Σenv j0 st0 with
             | None => None
             | Some (w, stw) =>
                 match compile_succs js0 stw with
                 | None => None
                 | Some (ws', st2) => Some (w :: ws', st2)
                 end
             end
         end) js st = Some (ws, st') ->
      (forall j0 st0 v0 st0', SC.supercompile_cfg fuel Σenv j0 st0 = Some (v0, st0') ->
        dom st0.(SC.sc_builder).(SC.cb_label) ⊆ dom st0'.(SC.sc_builder).(SC.cb_label)) ->
      dom st.(SC.sc_builder).(SC.cb_label) ⊆ dom st'.(SC.sc_builder).(SC.cb_label).
  Proof.
    intros fuel Σenv js.
    induction js as [|j js' IH]; intros st ws st' Hc Hstep.
    - simpl in Hc. injection Hc as _ ->. set_solver.
    - simpl in Hc.
      destruct (SC.supercompile_cfg fuel Σenv j st) as [[w stw]|] eqn:Hsc; [|discriminate].
      destruct ((fix compile_succs (js0 : list SC.config) (st0 : SC.sc_state) :=
                  match js0 with
                  | [] => Some ([], st0)
                  | j0 :: js0 =>
                      match SC.supercompile_cfg fuel Σenv j0 st0 with
                      | None => None
                      | Some (w0, stw0) =>
                          match compile_succs js0 stw0 with
                          | None => None
                          | Some (ws', st2) => Some (w0 :: ws', st2)
                          end
                      end
                  end) js' stw) as [[ws' st2]|] eqn:Hrest; [|discriminate].
      injection Hc as _ ->.
      etrans.
      + exact (Hstep j st w stw Hsc).
      + exact (IH stw ws' st' Hrest Hstep).
  Qed.

  Lemma supercompile_cfg_dom_mono :
    forall fuel Σenv j st v st',
      SC.supercompile_cfg fuel Σenv j st = Some (v, st') ->
      dom st.(SC.sc_builder).(SC.cb_label) ⊆ dom st'.(SC.sc_builder).(SC.cb_label).
  Proof.
    intro fuel.
    induction fuel as [|fuel' IH]; intros Σenv j st v st' Hsc.
    - (* fuel = 0 *)
      unfold SC.supercompile_cfg in Hsc.
      destruct (SC.memo_lookup _ _) as [vhit|] eqn:Hmemo.
      + injection Hsc as _ ->. set_solver.
      + destruct (SC.sc_alloc _ _) as [v0 st1] eqn:Halloc.
        injection Hsc as _ ->.
        apply (sc_alloc_dom_mono _ _ _ _ Halloc).
    - (* fuel = S fuel' *)
      unfold SC.supercompile_cfg in Hsc.
      fold SC.supercompile_cfg in Hsc.
      destruct (SC.memo_lookup _ _) as [vhit|] eqn:Hmemo.
      + injection Hsc as _ ->. set_solver.
      + destruct (SC.sc_alloc _ _) as [v0 st1] eqn:Halloc.
        cbn -[SC.sc_alloc SC.cb_fresh SC.cb_put_label SC.cb_put_succ SC.cb_put_inst SC.cb_put_holes SC.whistle_candidates SC.best_generalize SC.canon_config SC.norm_config SC.drive_step] in Hsc.
        set (jcanon := SC.canon_config (SC.norm_config SC.memo_norm_fuel Σenv j)) in *.
        set (cands := SC.whistle_candidates fuel' jcanon st.(SC.sc_memo)) in *.
        destruct (SC.best_generalize jcanon cands) as [[g v_prev]|] eqn:Hgen.
        * (* generalisation branch *)
          destruct (SC.sc_alloc g.(SC.gen_j) st1) as [vg stg0] eqn:Hallocg.
          set (bg1 := SC.cb_put_holes vg g.(SC.gen_holes) stg0.(SC.sc_builder)) in *.
          set (bg2 := SC.cb_put_succ v_prev [vg] bg1) in *.
          set (bg3 := SC.cb_put_inst v_prev g.(SC.gen_sub1) bg2) in *.
          set (bg4 := SC.cb_put_succ v0 [vg] bg3) in *.
          set (bg5 := SC.cb_put_inst v0 g.(SC.gen_sub2) bg4) in *.
          set (stg1 := {| SC.sc_builder := bg5; SC.sc_memo := stg0.(SC.sc_memo) |}) in *.
          set (nextg := SC.drive_step Σenv g.(SC.gen_j)) in *.
          destruct ((fix compile_succs (js : list SC.config) (st0 : SC.sc_state) {struct js} : option (list nat * SC.sc_state) :=
                      match js with
                      | [] => Some ([], st0)
                      | j0 :: js0 =>
                          match SC.supercompile_cfg fuel' Σenv j0 st0 with
                          | None => None
                          | Some (w, stw) =>
                              match compile_succs js0 stw with
                              | None => None
                              | Some (ws, st2) => Some (w :: ws, st2)
                              end
                          end
                      end) nextg stg1) as [[vsg stg2]|] eqn:Hcomp.
          -- (* success *)
             injection Hsc as <- <-.
             etrans; [apply (sc_alloc_dom_mono _ _ _ _ Halloc)|].
             etrans; [apply (sc_alloc_dom_mono _ _ _ _ Hallocg)|].
             etrans; [| apply (compile_succs_dom_mono fuel' Σenv nextg stg1 vsg stg2 Hcomp (IH Σenv))].
             subst stg1 bg5 bg4 bg3 bg2 bg1. cbn. set_solver.
          -- (* failure *)
             injection Hsc as <- <-.
             etrans; [apply (sc_alloc_dom_mono _ _ _ _ Halloc)|].
             etrans; [apply (sc_alloc_dom_mono _ _ _ _ Hallocg)|].
             subst stg1 bg5 bg4 bg3 bg2 bg1. cbn. set_solver.
        * (* no generalise branch *)
          set (next := SC.drive_step Σenv jcanon) in *.
          destruct ((fix compile_succs (js : list SC.config) (st0 : SC.sc_state) {struct js} : option (list nat * SC.sc_state) :=
                      match js with
                      | [] => Some ([], st0)
                      | j0 :: js0 =>
                          match SC.supercompile_cfg fuel' Σenv j0 st0 with
                          | None => None
                          | Some (w, stw) =>
                              match compile_succs js0 stw with
                              | None => None
                              | Some (ws, st2) => Some (w :: ws, st2)
                              end
                          end
                      end) next st1) as [[vs st2]|] eqn:Hcomp.
          -- (* success *)
             injection Hsc as <- <-.
             etrans; [apply (sc_alloc_dom_mono _ _ _ _ Halloc)|].
             etrans; [apply (compile_succs_dom_mono fuel' Σenv next st1 vs st2 Hcomp (IH Σenv))|].
             cbn. set_solver.
          -- (* failure *)
             injection Hsc as <- <-.
             apply (sc_alloc_dom_mono _ _ _ _ Halloc).
  Qed.


  (** Helper: compile_succs preserves well-formedness
  
      This is the key lemma showing that recursive compilation maintains
      the invariant that all returned vertices are in the label domain.
  *)
  Lemma compile_succs_preserves_wf :
    forall fuel Σenv js st ws st',
      (* If we can compile all successors *)
      (fix compile_succs (js : list SC.config) (st0 : SC.sc_state) :=
        match js with
        | [] => Some ([], st0)
        | j0 :: js0 =>
            match SC.supercompile_cfg fuel Σenv j0 st0 with
            | None => None
            | Some (w, stw) =>
                match compile_succs js0 stw with
                | None => None
                | Some (ws', st2) => Some (w :: ws', st2)
                end
            end
        end) js st = Some (ws, st') ->
      (* Assuming supercompile_cfg_well_formed holds *)
      (forall j0 st0 v0 st0',
        SC.supercompile_cfg fuel Σenv j0 st0 = Some (v0, st0') ->
        v0 ∈ dom st0'.(SC.sc_builder).(SC.cb_label)) ->
      (* Then all returned vertices exist in cb_label *)
      Forall (fun w => w ∈ dom st'.(SC.sc_builder).(SC.cb_label)) ws.
  Proof.
    intros fuel Σenv js.
    induction js as [|j js' IH].
    - (* Base case: empty list *)
      intros st ws st' Hcompile Hwf.
      simpl in Hcompile.
      injection Hcompile as Hws Hst'. subst.
      constructor.
    - (* Inductive case: j :: js' *)
      intros st ws st' Hcompile Hwf.
      simpl in Hcompile.
      destruct (SC.supercompile_cfg fuel Σenv j st) as [[w stw]|] eqn:Hsc; [|discriminate].
      destruct ((fix compile_succs (js0 : list SC.config) (st0 : SC.sc_state) :=
                  match js0 with
                  | [] => Some ([], st0)
                  | j0 :: js0 =>
                      match SC.supercompile_cfg fuel Σenv j0 st0 with
                      | None => None
                      | Some (w0, stw0) =>
                          match compile_succs js0 stw0 with
                          | None => None
                          | Some (ws', st2) => Some (w0 :: ws', st2)
                          end
                      end
                  end) js' stw) as [[ws' st2]|] eqn:Hrest; [|discriminate].
      injection Hcompile as Hws Hst'. subst ws st'.
      constructor.
      + (* Show w ∈ dom st2 *)
        (* We need to show that w is preserved from stw to st2 *)
        (* This requires supercompile_cfg_well_formed preservation part *)
        apply Hwf in Hsc.
        (* Now we need: w ∈ dom stw → w ∈ dom st2.
           This follows from domain monotonicity of [compile_succs]. *)
        pose proof (compile_succs_dom_mono fuel Σenv js' stw ws' st2 Hrest (supercompile_cfg_dom_mono fuel Σenv)) as Hmono.
        exact (Hmono _ Hsc).
      + (* Show Forall for ws' by IH *)
        apply (IH stw ws' st2 Hrest Hwf).
  Qed.

  (** Helper: memo_lookup returns vertices in domain *)
  Lemma memo_lookup_in_domain :
    forall j memo v,
      SC.memo_lookup j memo = Some v ->
      exists cfg, In (cfg, v) memo.
  Proof.
    intros j memo.
    induction memo as [|[cfg' v'] memo' IH].
    - intros v Hlookup. discriminate.
    - intros v Hlookup.
      unfold SC.memo_lookup in Hlookup.
      simpl in Hlookup.
      destruct (SC.judgement_eqb j cfg') eqn:Heq.
      + injection Hlookup as Hv. subst.
        exists cfg'. left. reflexivity.
      + fold SC.memo_lookup in Hlookup.
        apply IH in Hlookup.
        destruct Hlookup as [cfg Hin].
        exists cfg. right. exact Hin.
  Qed.
  
  (** Memo consistency: every memo entry has a corresponding label. *)
  Definition bounded_labels (st : SC.sc_state) : Prop :=
    forall v cfg, st.(SC.sc_builder).(SC.cb_label) !! v = Some cfg ->
      v < st.(SC.sc_builder).(SC.cb_next).

  Lemma bounded_labels_sc_init : bounded_labels SC.sc_init.
  Proof.
    intros v cfg Hv. cbn in Hv. rewrite lookup_empty in Hv. discriminate.
  Qed.
  Definition memo_sound (st : SC.sc_state) : Prop :=
    forall cfg v,
      In (cfg, v) st.(SC.sc_memo) ->
      st.(SC.sc_builder).(SC.cb_label) !! v = Some cfg.

  Lemma memo_sound_sc_init : memo_sound SC.sc_init.
  Proof.
    intros cfg v Hin.
    simpl in Hin. contradiction.
  Qed.

  Lemma memo_sound_sc_alloc (st st' : SC.sc_state) (cfg : SC.config) (v : nat) :
    memo_sound st ->
    bounded_labels st ->
    SC.sc_alloc cfg st = (v, st') ->
    memo_sound st'.
  Proof.
    intros Hsound Hbounded Halloc cfg' v' Hin.
    unfold SC.sc_alloc in Halloc.
    destruct (SC.cb_fresh st.(SC.sc_builder)) as [vf bf] eqn:Hfresh.
    injection Halloc as Hv Hst'. subst v st'.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    - inversion Hin. subst.
      unfold SC.cb_put_label. simpl.
      rewrite lookup_insert. reflexivity.
    - specialize (Hsound cfg' v' Hin).
      unfold SC.cb_put_label. simpl.
      unfold SC.cb_fresh in Hfresh.
      injection Hfresh as Hvf Hbf. subst bf.
      destruct (decide (v' = vf)) as [->|Hneq].
      + (* impossible: vf = cb_next st is fresh *)
        exfalso. subst vf.
        pose proof (Hbounded (SC.sc_builder st).(SC.cb_next) cfg' Hsound) as Hlt. lia.
      + rewrite lookup_insert_ne; [exact Hsound|intro Hc; apply Hneq; symmetry; exact Hc].
  Qed.

  Lemma memo_vertices_in_builder :
    forall st cfg v,
      memo_sound st ->
      In (cfg, v) st.(SC.sc_memo) ->
      v ∈ dom st.(SC.sc_builder).(SC.cb_label).
  Proof.
    intros st cfg v Hsound Hin.
    apply elem_of_dom.
    exists cfg.
    exact (Hsound cfg v Hin).
  Qed.
  
  (** Helper: cb_put_succ preserves cb_label domain *)
  Lemma cb_put_succ_preserves_label :
    forall b v succs w,
      w ∈ dom (SC.cb_label b) ->
      w ∈ dom (SC.cb_label (SC.cb_put_succ v succs b)).
  Proof.
    intros b v succs w Hw.
    unfold SC.cb_put_succ. simpl. exact Hw.
  Qed.
  
  (** Helper: cb_put_inst preserves cb_label domain *)
  Lemma cb_put_inst_preserves_label :
    forall b v σ w,
      w ∈ dom (SC.cb_label b) ->
      w ∈ dom (SC.cb_label (SC.cb_put_inst v σ b)).
  Proof.
    intros b v σ w Hw.
    unfold SC.cb_put_inst. simpl. exact Hw.
  Qed.
  
  (** Helper: cb_put_holes preserves cb_label domain *)
  Lemma cb_put_holes_preserves_label :
    forall b v hs w,
      w ∈ dom (SC.cb_label b) ->
      w ∈ dom (SC.cb_label (SC.cb_put_holes v hs b)).
  Proof.
    intros b v hs w Hw.
    unfold SC.cb_put_holes. simpl. exact Hw.
  Qed.
  
  (** Successor-closure for cfg builders. *)
  Definition builder_succ_closed (b : SC.cfg_builder) : Prop :=
    forall v succs,
      b.(SC.cb_succ) !! v = Some succs ->
      Forall (fun u => u ∈ dom b.(SC.cb_label)) succs.

  (** A well-formed supercompiler state: memo entries match labels, and all
      recorded successor edges point to labelled vertices. *)

  Lemma bounded_labels_sc_alloc (st st' : SC.sc_state) (cfg : SC.config) (v : nat) :
    bounded_labels st ->
    SC.sc_alloc cfg st = (v, st') ->
    bounded_labels st'.
  Proof.
    intros Hbounded Halloc.
    unfold SC.sc_alloc in Halloc.
    destruct (SC.cb_fresh st.(SC.sc_builder)) as [vf bf] eqn:Hfresh.
    unfold SC.cb_fresh in Hfresh.
    injection Hfresh as Hvf Hbf. subst vf bf.
    injection Halloc as <- <-.
    intros w cfgw Hw.
    cbn in Hw.
    destruct (decide (w = st.(SC.sc_builder).(SC.cb_next))) as [->|Hneq].
    - rewrite lookup_insert in Hw. injection Hw as <-.
      cbn. lia.
    - rewrite lookup_insert_ne in Hw; [|symmetry; exact Hneq].
      apply Hbounded in Hw.
      cbn. lia.
  Qed.

  Definition state_wf (st : SC.sc_state) : Prop :=
    memo_sound st /\ builder_succ_closed st.(SC.sc_builder) /\ bounded_labels st.

  (** Helper: compile_succs preserves [state_wf] and returns labelled vertices,
      given that each individual [supercompile_cfg] step does. *)
  Lemma compile_succs_state_wf :
    forall fuel Σenv js st ws st',
      (fix compile_succs (js : list SC.config) (st0 : SC.sc_state) {struct js} : option (list nat * SC.sc_state) :=
         match js with
         | [] => Some ([], st0)
         | j0 :: js0 =>
             match SC.supercompile_cfg fuel Σenv j0 st0 with
             | None => None
             | Some (w, stw) =>
                 match compile_succs js0 stw with
                 | None => None
                 | Some (ws', st2) => Some (w :: ws', st2)
                 end
             end
         end) js st = Some (ws, st') ->
      state_wf st ->
      (forall j0 st0 v0 st0',
         state_wf st0 ->
         SC.supercompile_cfg fuel Σenv j0 st0 = Some (v0, st0') ->
         state_wf st0' /\ v0 ∈ dom st0'.(SC.sc_builder).(SC.cb_label)) ->
      state_wf st' /\ Forall (fun w => w ∈ dom st'.(SC.sc_builder).(SC.cb_label)) ws.
  Proof.
    intros fuel Σenv js.
    induction js as [|j js' IH]; intros st ws st' Hc Hwf Hstep.
    - cbn in Hc. injection Hc as Hws Hst'. subst ws st'. split; [exact Hwf|constructor].
    - cbn in Hc.
      destruct (SC.supercompile_cfg fuel Σenv j st) as [[w stw]|] eqn:Hsc; [|discriminate].
      destruct ((fix compile_succs (js0 : list SC.config) (st0 : SC.sc_state) {struct js0} : option (list nat * SC.sc_state) :=
                  match js0 with
                  | [] => Some ([], st0)
                  | j0 :: js0 =>
                      match SC.supercompile_cfg fuel Σenv j0 st0 with
                      | None => None
                      | Some (w0, stw0) =>
                          match compile_succs js0 stw0 with
                          | None => None
                          | Some (ws', st2) => Some (w0 :: ws', st2)
                          end
                      end
                  end) js' stw) as [[ws' st2]|] eqn:Hrest; [|discriminate].
      injection Hc as Hws Hst'. subst ws st'.
      pose proof (Hstep j st w stw Hwf Hsc) as [HwfW Hwdom].
      destruct (IH stw ws' st2 Hrest HwfW Hstep) as [Hwf2 Hfor].
      split; [exact Hwf2|].
      constructor.
      + pose proof (compile_succs_dom_mono fuel Σenv js' stw ws' st2 Hrest (supercompile_cfg_dom_mono fuel Σenv)) as Hmono.
        exact (Hmono _ Hwdom).
      + exact Hfor.
  Qed.

  Lemma builder_succ_closed_empty : builder_succ_closed SC.cb_empty.
  Proof.
    intros v succs Hs.
    cbn in Hs.
    discriminate.
  Qed.

  Lemma builder_succ_closed_put_label (b : SC.cfg_builder) (v : nat) (cfg : SC.config) :
    builder_succ_closed b ->
    builder_succ_closed (SC.cb_put_label v cfg b).
  Proof.
    intros Hclosed w succs Hsucc.
    unfold SC.cb_put_label in Hsucc; cbn in Hsucc.
    specialize (Hclosed w succs Hsucc).
    eapply Forall_impl; [exact Hclosed|].
    intros u Hu.
    apply elem_of_dom in Hu as [cfg' Hcfg'].
    destruct (decide (u = v)) as [->|Hneq].
    - apply elem_of_dom. eexists cfg.
      unfold SC.cb_put_label; cbn.
      rewrite lookup_insert. reflexivity.
    - apply elem_of_dom. eexists cfg'.
      unfold SC.cb_put_label; cbn.
      rewrite lookup_insert_ne; [exact Hcfg'|symmetry; exact Hneq].
  Qed.

  Lemma builder_succ_closed_put_inst (b : SC.cfg_builder) (v : nat) (σ : list tm) :
    builder_succ_closed b ->
    builder_succ_closed (SC.cb_put_inst v σ b).
  Proof.
    intros Hclosed w succs Hsucc.
    unfold SC.cb_put_inst in Hsucc; cbn in Hsucc.
    exact (Hclosed w succs Hsucc).
  Qed.

  Lemma builder_succ_closed_put_holes (b : SC.cfg_builder) (v : nat) (hs : list tm) :
    builder_succ_closed b ->
    builder_succ_closed (SC.cb_put_holes v hs b).
  Proof.
    intros Hclosed w succs Hsucc.
    unfold SC.cb_put_holes in Hsucc; cbn in Hsucc.
    exact (Hclosed w succs Hsucc).
  Qed.

  Lemma builder_succ_closed_put_succ (b : SC.cfg_builder) (v : nat) (succs : list nat) :
    builder_succ_closed b ->
    Forall (fun u => u ∈ dom b.(SC.cb_label)) succs ->
    builder_succ_closed (SC.cb_put_succ v succs b).
  Proof.
    intros Hclosed Hsuccs w ws Hws.
    unfold SC.cb_put_succ in Hws; cbn in Hws.
    destruct (decide (w = v)) as [->|Hneq].
    - rewrite lookup_insert in Hws.
      inversion Hws; subst.
      exact Hsuccs.
    - rewrite lookup_insert_ne in Hws; [|symmetry; exact Hneq].
      exact (Hclosed w ws Hws).
  Qed.

  Lemma state_wf_sc_init : state_wf SC.sc_init.
  Proof.
    split.
    - exact memo_sound_sc_init.
    - split.
      + exact builder_succ_closed_empty.
      + exact bounded_labels_sc_init.
  Qed.

  Lemma state_wf_sc_alloc (st st' : SC.sc_state) (cfg : SC.config) (v : nat) :
    state_wf st ->
    SC.sc_alloc cfg st = (v, st') ->
    state_wf st'.
  Proof.
    intros [Hmemo [Hclosed Hbounded]] Halloc.
    split.
    - eapply memo_sound_sc_alloc; eauto.
    - split.
      + unfold SC.sc_alloc in Halloc.
        destruct (SC.cb_fresh st.(SC.sc_builder)) as [vf bf] eqn:Hfresh.
        unfold SC.cb_fresh in Hfresh.
        injection Hfresh as Hvf Hbf. subst vf bf.
        injection Halloc as _ Hst'.
        subst st'.
        cbn.
        apply builder_succ_closed_put_label.
        exact Hclosed.
      + eapply bounded_labels_sc_alloc; eauto.
  Qed.

  (** The main structural invariant: supercompilation preserves state well-formedness,
      and returns a vertex that is labelled in the resulting state. *)
  Lemma supercompile_cfg_well_formed :
    forall fuel Σenv j st v st',
      state_wf st ->
      SC.supercompile_cfg fuel Σenv j st = Some (v, st') ->
      state_wf st' /\ v ∈ dom st'.(SC.sc_builder).(SC.cb_label).
  Proof.
    intro fuel.
    induction fuel as [|fuel' IH]; intros Σenv j st v st' Hwf Hsc.
    - unfold SC.supercompile_cfg in Hsc.
      destruct (SC.memo_lookup _ _) as [vhit|] eqn:HmemoL.
      + injection Hsc as <- <-.
        split; [exact Hwf|].
        apply memo_lookup_in_domain in HmemoL.
        destruct HmemoL as [cfg Hin].
        apply elem_of_dom.
        exists cfg.
        exact (proj1 Hwf cfg vhit Hin).
      + destruct (SC.sc_alloc _ _) as [v0 st1] eqn:Halloc.
        injection Hsc as <- <-.
        split.
        * eapply state_wf_sc_alloc; eauto.
        * apply (sc_alloc_adds_label _ _ _ _ Halloc).
    - unfold SC.supercompile_cfg in Hsc.
      fold SC.supercompile_cfg in Hsc.
      destruct (SC.memo_lookup _ _) as [vhit|] eqn:HmemoL.
      + injection Hsc as <- <-.
        split; [exact Hwf|].
        apply memo_lookup_in_domain in HmemoL.
        destruct HmemoL as [cfg Hin].
        apply elem_of_dom.
        exists cfg.
        exact (proj1 Hwf cfg vhit Hin).
      + destruct (SC.sc_alloc _ _) as [v0 st1] eqn:Halloc.
        assert (Hwf1 : state_wf st1).
        { eapply state_wf_sc_alloc; eauto. }
        cbn -[SC.sc_alloc SC.cb_fresh SC.cb_put_label SC.cb_put_succ SC.cb_put_inst SC.cb_put_holes SC.whistle_candidates SC.best_generalize SC.canon_config SC.norm_config SC.drive_step] in Hsc.
        set (jcanon := SC.canon_config (SC.norm_config SC.memo_norm_fuel Σenv j)) in *.
        set (cands := SC.whistle_candidates fuel' jcanon st.(SC.sc_memo)) in *.
        destruct (SC.best_generalize jcanon cands) as [[g v_prev]|] eqn:Hgen.
          * (* generalisation branch *)
             destruct (SC.sc_alloc g.(SC.gen_j) st1) as [vg stg0] eqn:Hallocg.
             assert (Hwf_g0 : state_wf stg0).
             { eapply state_wf_sc_alloc; eauto. }
              set (bg1 := SC.cb_put_holes vg g.(SC.gen_holes) stg0.(SC.sc_builder)) in *.
              set (bg2 := SC.cb_put_succ v_prev [vg] bg1) in *.
              set (bg3 := SC.cb_put_inst v_prev g.(SC.gen_sub1) bg2) in *.
              set (bg4 := SC.cb_put_succ v0 [vg] bg3) in *.
              set (bg5 := SC.cb_put_inst v0 g.(SC.gen_sub2) bg4) in *.
              set (stg1 := {| SC.sc_builder := bg5; SC.sc_memo := stg0.(SC.sc_memo) |}) in *.
              assert (Hwf_g1 : state_wf stg1).
              { destruct Hwf_g0 as [Hmemo_g0 [Hsucc_g0 Hbound_g0]].
                repeat split.
                - (* memo_sound: stg1 shares stg0's memo and cb_label *)
                  exact Hmemo_g0.
                - (* builder_succ_closed: patching preserves closure *)
                  assert (Hvg_dom : vg ∈ dom stg0.(SC.sc_builder).(SC.cb_label)).
                  { apply (sc_alloc_adds_label _ _ _ _ Hallocg). }
                  assert (Hvg_succ : Forall (fun u => u ∈ dom stg0.(SC.sc_builder).(SC.cb_label)) [vg]).
                  { apply Forall_singleton. exact Hvg_dom. }
                  pose proof (builder_succ_closed_put_holes stg0.(SC.sc_builder) vg g.(SC.gen_holes) Hsucc_g0) as Hc1.
                  pose proof (builder_succ_closed_put_succ bg1 v_prev [vg] Hc1 Hvg_succ) as Hc2.
                  pose proof (builder_succ_closed_put_inst bg2 v_prev g.(SC.gen_sub1) Hc2) as Hc3.
                  pose proof (builder_succ_closed_put_succ bg3 v0 [vg] Hc3 Hvg_succ) as Hc4.
                  exact (builder_succ_closed_put_inst bg4 v0 g.(SC.gen_sub2) Hc4).
                - (* bounded_labels: stg1 shares stg0's cb_label and cb_next *)
                  exact Hbound_g0. }
             (* compile successors of generalised node; if it fails we keep stg1 *)
              set (nextg := SC.drive_step Σenv g.(SC.gen_j)) in *.
              destruct ((fix compile_succs (js : list SC.config) (st0 : SC.sc_state) {struct js} : option (list nat * SC.sc_state) :=
                          match js with
                          | [] => Some ([], st0)
                          | j0 :: js0 =>
                              match SC.supercompile_cfg fuel' Σenv j0 st0 with
                              | None => None
                              | Some (w, stw) =>
                                  match compile_succs js0 stw with
                                  | None => None
                                  | Some (ws, st2) => Some (w :: ws, st2)
                                  end
                              end
                          end) nextg stg1) as [[vsg stg2]|] eqn:Hcomp.
              -- (* success: add succs for vg *)
                 (* Prove that compile_succs preserves state_wf and returns dom-labelled vertices. *)
                 assert (Hcomp_wf : state_wf stg2 /\ Forall (fun w => w ∈ dom stg2.(SC.sc_builder).(SC.cb_label)) vsg).
                 { eapply compile_succs_state_wf; [exact Hcomp|exact Hwf_g1|].
                   intros jc stc vc stc' Hwfc Hscc. exact (IH _ _ _ _ _ Hwfc Hscc). }
                 destruct Hcomp_wf as [Hwf2 Hvsg].
                 destruct Hwf2 as [Hmemo2 [Hsucc2 Hbound2]].
                 injection Hsc as <- <-.
                 (* build final state_wf after cb_put_succ vg vsg *)
                 split.
                 ++ split.
                 ** exact Hmemo2.
                 ** split.
                    --- eapply builder_succ_closed_put_succ; [exact Hsucc2|exact Hvsg].
                    --- exact Hbound2.
                 ++ (* root vertex v0 remains labelled *)
                   (* v0 ∈ dom stg1.cb_label by construction, and compile_succs is dom-mono. *)
                   assert (Hv0_st1 : v0 ∈ dom st1.(SC.sc_builder).(SC.cb_label)).
                   { apply (sc_alloc_adds_label _ _ _ _ Halloc). }
                    assert (Hv0_stg0 : v0 ∈ dom stg0.(SC.sc_builder).(SC.cb_label)).
                    { (* stg0 extends st1 by a label insert *)
                      unfold SC.sc_alloc in Hallocg.
                      destruct (SC.cb_fresh st1.(SC.sc_builder)) as [vf bf] eqn:Hfresh.
                      unfold SC.cb_fresh in Hfresh.
                      injection Hfresh as Hvf Hbf. subst vf bf.
                      injection Hallocg as _ Hstg0'. subst.
                      simpl.
                      unfold SC.cb_put_label. cbn.
                       apply elem_of_dom in Hv0_st1 as [cfg Hv0cfg].
                       destruct (decide (v0 = st1.(SC.sc_builder).(SC.cb_next))) as [->|Hneq].
                       - apply elem_of_dom. eexists (SC.gen_j g).
                         rewrite lookup_insert. reflexivity.
                       - apply elem_of_dom. eexists cfg.
                         rewrite lookup_insert_ne; [exact Hv0cfg|symmetry; exact Hneq]. }
                   assert (Hv0_stg1 : v0 ∈ dom stg1.(SC.sc_builder).(SC.cb_label)).
                   { (* stg1 builder is bg5; cb_put_* preserve cb_label *)
                     subst stg1 bg5 bg4 bg3 bg2 bg1.
                     cbn.
                     exact Hv0_stg0. }
                   pose proof (compile_succs_dom_mono fuel' Σenv nextg stg1 vsg stg2 Hcomp (supercompile_cfg_dom_mono fuel' Σenv)) as Hmono.
                   exact (Hmono _ Hv0_stg1).
              -- (* compile_succs failed: keep stg1 *)
                 injection Hsc as <- <-.
                 split; [exact Hwf_g1|].
                 assert (Hv0_st1 : v0 ∈ dom st1.(SC.sc_builder).(SC.cb_label)).
                 { apply (sc_alloc_adds_label _ _ _ _ Halloc). }
                 assert (Hv0_stg0 : v0 ∈ dom stg0.(SC.sc_builder).(SC.cb_label)).
                 { apply (sc_alloc_dom_mono _ _ _ _ Hallocg). exact Hv0_st1. }
                 subst stg1 bg5 bg4 bg3 bg2 bg1.
                 cbn.
                 exact Hv0_stg0.
           * (* no generalise branch *)
              set (next := SC.drive_step Σenv jcanon) in *.
              destruct ((fix compile_succs (js : list SC.config) (st0 : SC.sc_state) {struct js} : option (list nat * SC.sc_state) :=
                          match js with
                          | [] => Some ([], st0)
                          | j0 :: js0 =>
                              match SC.supercompile_cfg fuel' Σenv j0 st0 with
                              | None => None
                              | Some (w, stw) =>
                                  match compile_succs js0 stw with
                                  | None => None
                                  | Some (ws, st2) => Some (w :: ws, st2)
                                  end
                              end
                           end) next st1) as [[vs st2]|] eqn:Hcomp.
              -- (* success *)
                 assert (Hcomp_wf : state_wf st2 /\ Forall (fun w => w ∈ dom st2.(SC.sc_builder).(SC.cb_label)) vs).
                 { eapply compile_succs_state_wf; [exact Hcomp|exact Hwf1|].
                   intros jc stc vc stc' Hwfc Hscc. exact (IH _ _ _ _ _ Hwfc Hscc). }
                  destruct Hcomp_wf as [Hwf2 Hvs].
                  destruct Hwf2 as [Hmemo2 [Hsucc2 Hbound2]].
                  injection Hsc as <- <-.
                  split.
                  ++ split.
                  ** exact Hmemo2.
                  ** split.
                     --- eapply builder_succ_closed_put_succ; [exact Hsucc2|exact Hvs].
                     --- exact Hbound2.
                  ++ (* root v0 remains in dom, and compile_succs is dom-mono *)
                    assert (Hv0_st1 : v0 ∈ dom st1.(SC.sc_builder).(SC.cb_label)).
                    { apply (sc_alloc_adds_label _ _ _ _ Halloc). }
                    pose proof (compile_succs_dom_mono fuel' Σenv next st1 vs st2 Hcomp (supercompile_cfg_dom_mono fuel' Σenv)) as Hmono.
                    exact (Hmono _ Hv0_st1).
              -- (* failure: keep st1 *)
                 injection Hsc as <- <-.
                 split; [exact Hwf1|].
                 apply (sc_alloc_adds_label _ _ _ _ Halloc).
  Qed.
 
  Theorem cfg_builder_well_formed :
    forall fuel Σenv Γ t A v scb,
      SC.supercompile_jTy fuel Σenv Γ t A = Some (v, scb) ->
      (forall w succs, scb.(SC.cb_succ) !! w = Some succs ->
        Forall (fun u => u ∈ dom scb.(SC.cb_label)) succs) /\
      v ∈ dom scb.(SC.cb_label).
  Proof.
    intros fuel Σenv Γ t A v scb Hsc.
    unfold SC.supercompile_jTy in Hsc.
    destruct (SC.supercompile_cfg fuel Σenv (C.jTy Γ t A) SC.sc_init) as [[v0 st0]|] eqn:Hcfg; [|discriminate].
    injection Hsc as <- Hscb. subst scb.
    pose proof (supercompile_cfg_well_formed fuel Σenv (C.jTy Γ t A) SC.sc_init v0 st0 state_wf_sc_init Hcfg)
      as [[_Hmemo [Hclosed _]] Hv0].
    split; [exact Hclosed|exact Hv0].
  Qed.
  
  (** Read-off produces graphs with well-formed successors.

      (See [ReadOffDrivingPreproofDefs.succ_of_closed] for the successor-closure
      invariant; it filters by [verts_of].)
  *)

End Correspondence.

(** Future work: Global soundness via trace condition

    Once we have local validity (above), we need to prove the global
    trace condition to get full cyclic proof soundness.
    
    This requires showing:
    1. Every cycle in the cfg_builder contains a progress edge (split)
    2. The trace ranking decreases on progress edges
    3. Therefore the cyclic proof is sound
    
    See theories/Transform/CyclicTraceCondition.v for the trace infrastructure.
*)

(** * Global soundness via budget trace condition *)

Section BudgetCyclicProof.

  Import CTB.

  Context (Σenv : Ty.env).
  Context (scb : SC.cfg_builder).
  Context (Hclosed : STC.builder_succ_closed scb).
  Context (Hcycle : forall xs,
    @FiniteDigraph.is_cycle nat _ _ (STC.cfg_graph scb Hclosed) xs ->
    Ranking.has_progress_edge nat (STC.progress_edge_cfg scb) xs).

  Definition cfg_budget : nat := stdpp.base.size (dom scb.(SC.cb_label)).
  Definition cfg_is_progress (v : nat) : bool := SC.is_progress_vertex scb v.

  Lemma progress_cfg_to_base (v w : nat) :
    STC.progress_edge_cfg scb v w <->
    progress_edge_base cfg_is_progress v w.
  Proof. unfold STC.progress_edge_cfg, progress_edge_base, cfg_is_progress. reflexivity. Qed.

  Lemma progress_cfg_has_to_base (xs : list nat) :
    Ranking.has_progress_edge nat (STC.progress_edge_cfg scb) xs ->
    Ranking.has_progress_edge nat
      (progress_edge_base cfg_is_progress) xs.
  Proof.
    intros Hprog. induction xs as [|v xs IH]; [contradiction|].
    destruct xs as [|w xs']; cbn in Hprog. { contradiction. }
    destruct Hprog as [Hhead | Htail].
    - cbn. left. apply progress_cfg_to_base. exact Hhead.
    - cbn. right. apply IH. exact Htail.
  Qed.

  Lemma cfg_ranking_condition :
    @Ranking.ranking_condition ((nat * nat)%type) _ _
      (trace_graph (STC.cfg_graph scb Hclosed) cfg_is_progress cfg_budget)
      (progress_edge_trace cfg_is_progress)
      nat lt
      rank_trace.
  Proof using scb Hclosed Hcycle.
    apply (budget_trace_ranking_condition (STC.cfg_graph scb Hclosed) cfg_is_progress cfg_budget).
    intros xs Hcyc. apply progress_cfg_has_to_base. apply Hcycle. exact Hcyc.
  Qed.

  Definition trace_label (vk : nat * nat) : config :=
    let '(v, _) := vk in sc_pp_label scb v.

  Definition trace_digraph : @FiniteDigraph.fin_digraph (nat * nat)%type _ _ :=
    trace_graph (STC.cfg_graph scb Hclosed) cfg_is_progress cfg_budget.

  (** Local validity of the trace graph: every trace vertex satisfies the
      configuration drive rule against its trace successors.

      NOTE: this is an open invariant.  It follows from
      [vertex_drive_rule_holds Σenv scb] together with a correct treatment of
      budget-cutoff vertices (a progress vertex at budget 0 has no trace
      successors, so its rule is a backlink, not [dr_leaf]). *)
  Context (Hrule_ok : forall vk,
    vk ∈ verts trace_digraph ->
    sc_rule Σenv (trace_label vk) (map trace_label (succ trace_digraph vk))).

  Definition trace_preproof :
    @Preproof.preproof config (sc_rule Σenv) (nat * nat)%type _ _ :=
    {| Preproof.pp_graph := trace_digraph; Preproof.pp_label := trace_label;
       Preproof.pp_rule_ok := Hrule_ok |}.

  Context (v_root : nat).
  Context (Hv_root : v_root ∈ sc_verts scb).

  Lemma trace_root_in_verts : (v_root, cfg_budget) ∈ verts trace_digraph.
  Proof using Hclosed Hv_root scb v_root.
    unfold trace_digraph, trace_graph. cbn. apply elem_of_list_to_set. apply elem_of_in_prod.
    - apply elem_of_elements. unfold sc_verts in Hv_root. unfold STC.cfg_graph. cbn. exact Hv_root.
    - apply (proj2 (elem_of_list_In _ _)). apply in_seq. lia.
  Qed.

  Definition trace_progress_edge
    (p : @Preproof.preproof config (sc_rule Σenv) (nat * nat)%type _ _)
    (vk wk : nat * nat) : Prop :=
    progress_edge_trace cfg_is_progress vk wk.

  Definition sc_cyclic_proof :
     @Ranked.cyclic_proof config (sc_rule Σenv) (nat * nat)%type _ _ trace_progress_edge.
  Proof using Hclosed Hcycle Hrule_ok scb Σenv.
    refine {| CyclicProof.cp_preproof := trace_preproof;
              CyclicProof.cp_witness := {| Ranked.rw_M := nat; Ranked.rw_lt := lt; Ranked.rw_rank := snd |};
              CyclicProof.cp_progress_ok := _ |}.
    unfold Ranked.progress_ok. cbn. apply cfg_ranking_condition.
  Defined.

  Definition sc_rooted_cyclic_proof :
    @Ranked.rooted_cyclic_proof config (sc_rule Σenv) (nat * nat)%type _ _ trace_progress_edge.
  Proof using Hclosed Hcycle Hrule_ok Hv_root scb v_root Σenv.
    refine {| CyclicProof.rcp_proof := sc_cyclic_proof;
              CyclicProof.rcp_root := (v_root, cfg_budget); CyclicProof.rcp_root_in := _ |}.
    change ((v_root, cfg_budget) ∈ verts trace_digraph). exact trace_root_in_verts.
  Defined.

End BudgetCyclicProof.

Theorem supercompile_yields_cyclic_proof :
  forall Σenv fuel Γ t A v scb,
    SC.supercompile_jTy_tc fuel Σenv Γ t A = Some (v, scb) ->
    @Ranked.cyclic_proof config (sc_rule Σenv) (nat * nat)%type _ _
      (trace_progress_edge Σenv scb).
Proof.
  (* TODO: needs the trace-level local-validity invariant [Hrule_ok], which
     follows from [vertex_drive_rule_holds Σenv scb] plus budget-cutoff
     handling for progress vertices at budget 0. *)
  Admitted.

Theorem supercompile_yields_rooted_cyclic_proof :
  forall Σenv fuel Γ t A v scb,
    SC.supercompile_jTy_tc fuel Σenv Γ t A = Some (v, scb) ->
    @Ranked.rooted_cyclic_proof config (sc_rule Σenv) (nat * nat)%type _ _
      (trace_progress_edge Σenv scb).
Proof.
  (* TODO: same gap as [supercompile_yields_cyclic_proof]. *)
  Admitted.

(** * Claim 3: CIU Soundness *)

Section CIUSoundness.

  Lemma drive_cbn_once_ciu (t u : tm) :
    SC.drive_cbn_once t = u -> ciu t u.
  Proof.
    intro Hdr. apply steps_ciu. apply SDR.drive_cbn_onceR_steps.
    apply (drive_cbn_once_sound t u Hdr).
  Qed.

  Lemma whnf_drive_ciu (k : nat) (t : tm) : ciu t (SC.whnf_drive k t).
  Proof.
    revert t. induction k as [|k' IH]; intros t; cbn.
    - apply ciu_refl.
    - destruct (SC.tm_eqb t (SC.drive_cbn_once t)) eqn:Heq.
      + apply ciu_refl.
      + pose proof (drive_cbn_once_ciu t (SC.drive_cbn_once t) eq_refl) as Hci1.
        pose proof (IH (SC.drive_cbn_once t)) as Hci2. eapply ciu_trans; [exact Hci1|exact Hci2].
  Qed.

  (** Generalisation CIU: [apps (mk_lams tys body) args] β-reduces to
      [body] with arguments substituted sequentially via [subst0].
      Each [tLam] consumes one argument from [args]. *)
  Lemma ciu_generalise (tys args : list tm) (body : tm) :
    ciu (Cbn.apps (SC.mk_lams tys body) args) (fold_right subst0 body args).
  Proof.
    (* TODO: requires [length args = length tys] (the generalisation invariant);
       the base case with [args] longer than [tys] is unprovable as stated. *)
    Admitted.

  Lemma residualise_cfg_ciu (fuel : nat) (Σ : Ty.env) (b : SC.cfg_builder)
      (Hclosed : STC.builder_succ_closed b) (Hok : SC.trace_condition_ok b = true) :
    forall (v d : nat) (ρ : SC.fix_env) (Γ : Ty.ctx) (t A : tm),
      SC.lookup_label b v = Some (C.jTy Γ t A) ->
      ρ !! v = None ->
      ciu (shift d 0 t) (SC.residualise_cfg fuel Σ b v d ρ).
  Proof.
    (* TODO: needs [fuel > 0] (the base case [residualise_cfg 0 _ = tVar 0] is not
       CIU-related to [shift d 0 t]) plus the full induction over
       [residualise_cfg]/[residualise_cfg_core].  Claim-3 (CIU soundness) is
       incomplete. *)
    Admitted.

  Theorem supercompile_ciu_soundness_untyped :
    forall Σenv fuel_sc fuel_res Γ t A v scb,
      SC.supercompile_jTy_tc fuel_sc Σenv Γ t A = Some (v, scb) ->
      ciu t (SC.residualise_cfg fuel_res Σenv scb v 0 (∅ : SC.fix_env)).
  Proof.
    (* TODO: depends on [residualise_cfg_ciu] (Claim-3 CIU soundness, incomplete);
       also requires relating the root's canonicalised label to the input [t]. *)
    Admitted.

End CIUSoundness.

(** * Typing Preservation for the Residualiser *)

Section ResidualiserTyping.

  (** Regularity: if [has_type Σ Γ t A], then A is well-sorted.
      This follows by induction on the typing derivation, extracting the
      sort level from each rule. For the [tFix] case, the rule already
      requires [has_type Σ Γ A (tSort i)] as a premise. *)
  Lemma residualise_cfg_root_typing (fuel : nat) (Σenv : Ty.env) (b : SC.cfg_builder)
      (Γ : Ty.ctx) (t A : tm) (v : nat) (i : nat)
      (Hclosed : Ty.closed_param_tys Σenv) :
    fuel > 0 ->
    SC.lookup_label b v = Some (C.jTy Γ t A) ->
    SC.lookup_succ b v = None \/ SC.lookup_succ b v = Some [] ->
    Ty.has_type Σenv Γ t A ->
    Ty.has_type Σenv Γ A (tSort i) ->
    Ty.has_type Σenv Γ (SC.residualise_cfg fuel Σenv b v 0 (∅ : SC.fix_env)) A.
  Proof.
    (* TODO: Claim-4 (residualiser typing preservation) is incomplete. *)
    Admitted.

End ResidualiserTyping.

(** * Typed CIU Soundness

    Follows directly from the untyped CIU theorem: since [ciu] quantifies
    over all [var → tm] substitutions, instantiating with the list-based
    substitution [sub_fun (0, σ)] used by [ciu_jTy] gives the typed result.
*)

Section TypedCIU.

  Lemma subst_list_eq (σ : list tm) (t : tm) :
    Ty.subst_list σ t = t.[Ty.sub_fun (0, σ)].
  Proof. reflexivity. Qed.

  Theorem supercompile_ciu_soundness_typed :
    forall Σenv fuel_sc fuel_res Γ t A v scb,
      SC.supercompile_jTy_tc fuel_sc Σenv Γ t A = Some (v, scb) ->
      ciu_jTy Σenv Γ t (SC.residualise_cfg fuel_res Σenv scb v 0 (∅ : SC.fix_env)) A.
  Proof.
    intros Σenv fuel_sc fuel_res Γ t A v scb Hsc.
    pose proof (supercompile_ciu_soundness_untyped Σenv fuel_sc fuel_res Γ t A v scb Hsc) as Hciu.
    destruct Hciu as [Htu Hut].
    split.
    - intros Δ σ v' Hsub Hval Hterm.
      rewrite subst_list_eq in Hterm.
      apply Htu with (σ := Ty.sub_fun (0, σ)) (v := v').
      exact Hterm.
    - intros Δ σ v' Hsub Hval Hterm.
      rewrite subst_list_eq in Hterm.
      apply Hut with (σ := Ty.sub_fun (0, σ)) (v := v').
      exact Hterm.
  Qed.

End TypedCIU.
