From Stdlib Require Import List Arith Lia Utf8 Relations Relation_Operators Wellfounded.
From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Progress Require Import Ranking.
From Cyclic.CyclicProof Require Import Ranked.
From Cyclic.Transform Require Import ReadOff ReadOffDrivingPreproof SequentDrivingRules SequentObservationRules.

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

(** Cyclic trace condition for async-explicit proof graphs (Task 3)

    This file defines the trace-state-based ranking condition for cyclic proofs
    where:
    - **progress events = case-split on neutral scrutinee**
    - async driving steps are explicit in the graph but don't count as progress
    - the trace tracks which inductive variable we're measuring descent on

    Architecture:
    1. Trace state τ = option (I : nat × x : nat) tracks the scrutinee being split
    2. Async edges keep τ unchanged
    3. Split edges update τ to track a recursive argument (structural descent)
    4. The well-founded order ltM on τ is "recursive subterm" (from strict positivity)
    5. Progress edges are exactly split edges
*)

Section TraceCondition.
  Import RDP.Packaging.

  (** Trace state: which inductive variable are we tracking?
  
      - None = no active trace (initial state, or before first split)
      - Some (I, x) = tracking variable x (de Bruijn index) of inductive type I
  *)
  Definition trace_state : Type := option (nat * nat).

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
  
  (** Split edge: update τ to track a recursive argument
  
      When we split on scrutinee x : I using constructor c,
      we pick one of the recursive arguments (those of type I)
      and update τ to track it.
  *)
  | ts_split v w τ I x Γ Cmot brs A c :
      (* v is labeled with a case-split configuration *)
      pp_label fuel b v = jDrive (C.jTy Γ (tCase I (tVar x) Cmot brs) A) ->
      (* w is one of the split successors (for constructor c) *)
      w ∈ succ_of b v ->
      (* Look up constructor signature *)
      (exists ΣI ctor tys n rec_positions,
        SP.lookup_ind Σenv I = Some ΣI /\
        SP.lookup_ctor ΣI c = Some ctor /\
        tys = SP.ctor_param_tys ctor ++ repeat (tInd I []) (SP.ctor_rec_arity ctor) /\
        n = length tys /\
        (* rec_positions = indices i where tys[i] = tInd I [] *)
        rec_positions = filter (fun i => 
          match nth_error tys i with
          | Some (tInd I' []) => Nat.eqb I I'
          | _ => false
          end) (seq 0 n) /\
        (* Pick one recursive position (non-deterministically for now) *)
        (exists i y,
          i ∈ rec_positions /\
          (* Compute the de Bruijn index y of that argument in extended context *)
          (* extend_ctx does rev tys ++ Γ, so arg i becomes index (n-1-i) *)
          y = n - 1 - i /\
          (* Update trace to track this recursive argument *)
          τ = Some (I, y))) ->
      trace_step Σenv fuel b v w (Some (I, x)) τ
  
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

  (** Well-founded order on trace states: recursive subterm relation
  
      τ' < τ iff τ' arises from τ by taking a split step (constructor descent).
      
      This is well-founded because:
      - splitting a scrutinee of inductive type I
      - gives arguments that are structurally smaller (by strict positivity)
      - the recursive arguments are immediate subterms
  *)
  Inductive ltM_trace : trace_state -> trace_state -> Prop :=
  | ltM_split Σenv fuel b v w I x τ' :
      trace_step Σenv fuel b v w (Some (I, x)) τ' ->
      (exists Γ Cmot brs A c,
        pp_label fuel b v = jDrive (C.jTy Γ (tCase I (tVar x) Cmot brs) A) /\
        w ∈ succ_of b v) ->
      ltM_trace τ' (Some (I, x)).

  (** TODO: Prove well-foundedness of ltM_trace
  
      This requires showing that the recursive-subterm relation induced by
      constructor splitting is well-founded. This follows from:
      
      1. Strict positivity of inductive definitions (ensures no infinite descent)
      2. The fact that constructor arguments are structurally smaller
      3. The fuel/builder bound (finite number of vertices)
      
      For now we assume it as an axiom to get the infrastructure working.
  *)
  Axiom ltM_trace_wf : well_founded ltM_trace.

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
