From Stdlib Require Import List Arith Lia Utf8 Relations Relation_Operators Wellfounded.
From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Progress Require Import Ranking.
From Cyclic.CyclicProof Require Import Ranked.
From Cyclic.Transform Require Import ReadOff ReadOffDrivingPreproof SequentDrivingRules SequentObservationRules CyclicTraceConditionObsTree.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module RDP := ReadOffDrivingPreproof.
Module SDR := SequentDrivingRules.
Module SOR := SequentObservationRules.
Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module SP := StrictPos.
Module CTO := CyclicTraceConditionObsTree.

(** Cyclic trace condition for async-explicit proof graphs (Task 3)

    This file defines the trace-state-based ranking condition for cyclic proofs
    where:
    - **progress events = case-split on neutral scrutinee**
    - async driving steps are explicit in the graph but don't count as progress

    In this version, we prepare an observation-tree based ranking domain:

    - trace state τ = option [obs_tree]
    - progress steps select a recursive observation subtree
    - strict decrease is justified via [obs_size]

    This replaces the previous axiomatised "subterm" well-foundedness.
*)

Section TraceCondition.
  Import RDP.Packaging.

  (** Trace state: a (possibly absent) observation tree.

      Intuition: progress corresponds to descending into one of the recursive
      sub-observations of a constructor observation.
  *)
  Definition trace_state : Type := option SOR.obs_tree.

  (** Trace transition: how does τ update along an edge?
  
      This depends on the local rule instance at the source vertex.
  *)
  Inductive trace_step (Σenv : Ty.env) (fuel : nat) (b : RO.builder)
      : V -> V -> trace_state -> trace_state -> Prop :=
  
  (** Async edges: no change to trace state *)
  | ts_async v w τ :
      (* v is labeled with a configuration *)
      (exists Γ t A,
        pp_label fuel b v = jDrive (C.jTy Γ t A) /\
        (* and the rule at v is a single-premise async driving rule *)
        (* (not a split, not a fold) *)
        (* For now, we accept any 1-successor case as async *)
        length (succ_of b v) = 1 /\
        w ∈ succ_of b v) ->
      trace_step Σenv fuel b v w τ τ
  
  (** Split edge: descend into a recursive observation subtree.

      This is the shape needed for an [obs_tree]-based ranking: a progress step
      picks one of the recursive sub-observations, which is strictly smaller.

      (How this relates to the supercompiler/proof graph labels is wired up in
      later correspondence lemmas; here we only define the trace transition.)
  *)
  | ts_split v w c recs o Γ I x Cmot brs A :
      (* v is labeled with a case-split configuration *)
      pp_label fuel b v = jDrive (C.jTy Γ (tCase I (tVar x) Cmot brs) A) ->
      (* w is one of the split successors *)
      w ∈ succ_of b v ->
      (* the trace carries an observation tree whose root matches constructor c *)
      In o recs ->
      trace_step Σenv fuel b v w (Some (SOR.obsCtor c recs)) (Some o)
  
  (** Fold/backlink edge: no progress by itself
      (cycles without splits are rejected by the global condition)
  *)
  | ts_fold v w τ :
      (* v is labeled with a backlink node *)
      label_of b v = RO.nBack ->
      w ∈ succ_of b v ->
      trace_step Σenv fuel b v w τ τ.

  (** Progress edge: exactly the split edges *)
  Definition progress_edge_trace (Σenv : Ty.env) (fuel : nat) (b : RO.builder)
      (v w : V) (τ τ' : trace_state) : Prop :=
    exists I x Γ Cmot brs A c,
      pp_label fuel b v = jDrive (C.jTy Γ (tCase I (tVar x) Cmot brs) A) /\
      w ∈ succ_of b v /\
      trace_step Σenv fuel b v w τ τ'.

  (** Well-founded order on trace states.

      We use the strict subtree order induced by [obs_size] (see
      [Transform/CyclicTraceConditionObsTree.v]).
  *)
  Definition ltM_trace : trace_state -> trace_state -> Prop := CTO.lt_trace.

  Lemma ltM_trace_wf : well_founded ltM_trace.
  Proof.
    exact CTO.lt_trace_wf.
  Qed.

  Lemma ltM_trace_of_ts_split Σenv fuel b v w c recs o Γ I x Cmot brs A :
    trace_step Σenv fuel b v w (Some (SOR.obsCtor c recs)) (Some o) ->
    ltM_trace (Some o) (Some (SOR.obsCtor c recs)).
  Proof.
    intro Hstep.
    inversion Hstep; subst; try contradiction.
    unfold ltM_trace.
    unfold CTO.lt_trace.
    cbn.
    apply CTO.lt_obs_of_in_recs.
    assumption.
  Qed.

  (** Rank function: just project the trace state
  
      For nat-ranking, we'd need to map trace states to nat.
      For now, use the trace state directly as the ranking domain.
  *)
  Definition rank_trace (τ : trace_state) : trace_state := τ.

  (** The ranking witness for a preproof with explicit trace tracking *)
  Definition trace_ranking_witness : Ranked.ranking_witness (V := (V * trace_state)) :=
    {| Ranked.rw_M := trace_state;
       Ranked.rw_lt := ltM_trace;
       Ranked.rw_rank := snd |}.  (* rank projects the trace component *)

  (** Simplified ranking condition for cfg graphs.

      Instead of building an explicit trace graph with (V, τ) pairs, we provide
      a ranking function directly on base vertices and prove the conditions
      locally.

      This approach works when:
      - We already have cycle-progress (from the boolean trace check)
      - We can assign a rank to each vertex based on its label
      - Progress edges strictly decrease the rank
  *)
  Section SimplifiedRanking.
    Context (Σenv : Ty.env) (fuel : nat) (b : RO.builder).

    (** Assign a rank to each vertex based on its label.

        For now, use a dummy constant rank. A real implementation would:
        - Extract the observation tree from jIndObs labels
        - Use None for non-observation vertices
        - Prove that progress edges (splits) strictly decrease the tree size
    *)
    Definition vertex_rank (v : V) : trace_state := None.

    (** Progress edges for the base graph (not trace graph). *)
    Definition is_progress_edge (v w : V) : Prop :=
      exists I x Γ Cmot brs A,
        pp_label fuel b v = jDrive (C.jTy Γ (tCase I (tVar x) Cmot brs) A) /\
        w ∈ succ_of b v.

    (** If we can show:
        1. well_founded ltM_trace (done: ltM_trace_wf)
        2. rank monotone on all edges
        3. rank strictly decreases on progress edges
        4. every cycle has a progress edge (given by trace check)

        Then we have a full ranking_condition witness.

        For now, we state this as a lemma schema that can be instantiated
        once we have concrete observation-tree extraction.
    *)
    Lemma ranking_condition_schema :
      (forall v w, w ∈ succ_of b v -> 
         Ranking.leM ltM_trace (vertex_rank w) (vertex_rank v)) ->
      (forall v w, is_progress_edge v w ->
         ltM_trace (vertex_rank w) (vertex_rank v)) ->
      (forall xs, FiniteDigraph.is_cycle (graph_of b) xs ->
         Ranking.has_progress_edge (fun v w => is_progress_edge v w) xs) ->
      @Ranking.ranking_condition V _ _
        (graph_of b)
        (fun v w => is_progress_edge v w)
        trace_state
        ltM_trace
        vertex_rank.
    Proof.
      intros Hmon Hstrict Hcycle.
      refine {| Ranking.rc_wf := ltM_trace_wf;
                Ranking.rc_monotone := _;
                Ranking.rc_strict := _;
                Ranking.rc_cycle_progress := Hcycle |}.
      - intros v w Hedge.
        apply Hmon.
        destruct Hedge as [Hv Hw].
        exact Hw.
      - intros v w Hedge Hprog.
        apply Hstrict.
        exact Hprog.
    Qed.

  End SimplifiedRanking.

End TraceCondition.

(** Example: length (map f l) fusion (from CIUChecklistLengthMap)

    Goal: construct the trace graph for the supercompilation of
    `length (map f l)` and verify the ranking condition.
    
    Key steps in the supercompilation:
    1. Unfold map → case on l (PROGRESS: split on l at index 0)
    2. Nil branch: length nil → 0
    3. Cons branch: length (cons (f x) (map f xs))
       - case on cons → succ (length (map f xs))
       - recursive call: length (map f xs) (PROGRESS: split on xs at index 2)
    4. Fold back to step 1 (but tracking xs now, not l)
    
    The cycle is: split l → cons branch → recursive call → fold to split xs
    Progress: each iteration splits on a list variable (l, then xs, then ...)
    Rank: the list being split is structurally smaller each time
*)
Section Example_LengthMap.
  Import RDP.Packaging.
  
  From Cyclic.Syntax Require Import ListNat Examples.
  From Cyclic.Transform Require Import Supercompile.
  
  Definition Σ_listnat : Ty.env := [Examples.Nat_sig; ListNat.List_sig].
  Definition Γ_listnat : Ty.ctx := [ListNat.list_ty; ListNat.nat2nat].
  
  Definition t_len_map : tm :=
    tApp ListNat.length (tApp (tApp ListNat.map (tVar 1)) (tVar 0)).
  
  (** Construct the rooted preproof (locally-valid proof graph) *)
  Definition proof_len_map : rooted_preproof Σ_listnat t_len_map :=
    rooted_preproof_of Σ_listnat t_len_map.
  
  (** TODO: Construct the trace graph
  
      This requires:
      1. Identifying split nodes in the proof graph
      2. For each split, choosing which recursive argument to track
      3. Building the trace graph with (V, τ) vertices
      4. Defining progress edges on the trace graph
      5. Proving the ranking condition
  *)
  
  (** TODO: The ranking condition instance *)
  (*
  Lemma ranking_condition_len_map :
    @Ranking.ranking_condition (V * trace_state) _ _
      (trace_graph proof_len_map)
      (progress_edge_on_trace_graph proof_len_map)
      trace_state
      ltM_trace
      (fun '(_, τ) => τ).
  *)
  
End Example_LengthMap.
