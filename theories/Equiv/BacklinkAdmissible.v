From Stdlib Require Import List Bool Arith Lia Utf8.
From stdpp Require Import gmap.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile CyclicTraceConditionBudget.
From Cyclic.CyclicProof Require Import Ranked.
From Cyclic.Graph Require Import FiniteDigraph.
Import Term.Syntax.
Import ListNotations.
Set Default Proof Using "Type".

(** * Backlink Admissibility for CoC with Inductives *)

Module BacklinkAdmissible.

  Module SC := Supercompile.
  Module Ty := Typing.Typing.
  Module C := Ty.Cyclic.

  (** Extract the inductive type split at a progress vertex. *)
  Definition split_inductive (b : SC.cfg_builder) (v : nat) : option nat :=
    match SC.lookup_label b v with
    | Some (C.jTy _ (tCase I (tVar _) _ _) _) =>
        if SC.is_progress_vertex b v then Some I else None
    | _ => None
    end.

  (** * Lexicographic ranking on lifted vertices (v, k)

      The budget trace (Claim 2) lifts each vertex v to pairs (v, k)
      where k ∈ [0, B] is a budget counter.  Progress edges consume
      budget (k decreases), non-progress edges preserve it.

      We work on the lifted trace graph directly: the per-type rank
      is simply k, and the lexicographic ranking is well-founded
      because k cannot go below 0. *)

  Module CTB := CyclicTraceConditionBudget.

  Notation traceV := (nat * nat)%type.

  Definition per_type_rank (vk : traceV) : nat := snd vk.

  (** The base graph has no single per-vertex budget.  The budget
      is defined on LIFTED vertices (v, k).  For progress edges:
      (v1, k1) → (v2, k2) with k2 < k1 (budget decreases). *)

  (** The budget trace graph has the property that for any edge,
      the counter never increases, and on progress edges it strictly
      decreases. *)
  Lemma trace_rank_monotone :
    forall (G : FiniteDigraph.fin_digraph) (is_progress : nat -> bool) (B : nat) vk wk,
      FiniteDigraph.edge (CTB.trace_graph G is_progress B) vk wk ->
      snd wk <= snd vk.
  Proof.
    apply CTB.trace_rank_monotone.
  Qed.

  Lemma trace_rank_strict_on_progress :
    forall (G : FiniteDigraph.fin_digraph) (is_progress : nat -> bool) (B : nat) vk wk,
      FiniteDigraph.edge (CTB.trace_graph G is_progress B) vk wk ->
      CTB.progress_edge_trace G is_progress B vk wk ->
      snd wk < snd vk.
  Proof.
    apply CTB.trace_rank_strict_on_progress.
  Qed.

  Lemma progress_edge_decreases_rank :
    forall (G : FiniteDigraph.fin_digraph) (is_progress : nat -> bool) (B : nat) vk wk,
      FiniteDigraph.edge (CTB.trace_graph G is_progress B) vk wk ->
      CTB.progress_edge_trace G is_progress B vk wk ->
      per_type_rank wk < per_type_rank vk.
  Proof.
    intros G is_progress B vk wk Hedge Hprog.
    unfold per_type_rank.
    apply (trace_rank_strict_on_progress G is_progress B vk wk Hedge Hprog).
  Qed.

  (** Lexicographic less-than on lists of (inductive, rank) pairs. *)
  Inductive lex_lt : list (nat * nat) -> list (nat * nat) -> Prop :=
  | lex_lt_here : forall I r1 r2 rs1 rs2,
      r1 < r2 ->
      lex_lt ((I, r1) :: rs1) ((I, r2) :: rs2)
  | lex_lt_later : forall I r rs1 rs2,
      lex_lt rs1 rs2 ->
      lex_lt ((I, r) :: rs1) ((I, r) :: rs2).

  Lemma lex_lt_wf : well_founded lex_lt.
  Proof.
    intro a.
    remember (length a) as n.
    revert a Heqn.
    induction n as [|n IH] using (well_founded_induction lt_wf).
    intros a Hlen.
    constructor.
  Lemma trace_rank_monotone :
    forall (G : FiniteDigraph.fin_digraph) (is_progress : nat -> bool) (B : nat) vk wk,
      FiniteDigraph.edge (CTB.trace_graph G is_progress B) vk wk ->
      snd wk <= snd vk.
  Proof.
    apply CTB.trace_rank_monotone.
  Qed.

(** The budget trace lifted graph. *)
  Definition lifted_graph (scb : SC.cfg_builder) (Hclosed : SC.builder_succ_closed scb) : 
    @FiniteDigraph.fin_digraph traceV _ _ :=
    let G := CTB.cfg_graph scb Hclosed in
    let B := size (dom scb.(SC.cb_label)) in
    CTB.trace_graph G (SC.is_progress_vertex scb) B.

  (** Unfolding invariant: for each vertex vk in the lifted graph,
      there exists a term that is the result of "driving" the
      original config at v through all non-progress edges and
      replacing all backlinks with recursive calls. *)
  Definition unfolds_to (scb : SC.cfg_builder)
             (Gtrace : @FiniteDigraph.fin_digraph traceV _ _)
             (vk : traceV) (t : Term.Syntax.tm) : Prop :=
    (* Placeholder: t is the standard-proof term extracted from vk *)
    True.

  (** * Main theorem: Backlink admissibility

      For every SC-produced cyclic proof (cfg_builder scb passing
      trace_condition_ok), the root term t_original is CIU-equivalent
      to a term t_standard that uses only the CIC recursor (no
      cyclic backlinks).

      The proof constructs t_standard by traversing the budget-trace
      lifted graph in order of decreasing budget k.  At each vertex:
      - Progress vertices (case-splits): replaced by the CIC recursor
        for the inductive type, with base/step cases from successors.
      - Non-progress vertices: the SC's driving step is applied (β, ι,
        fix-unfold, etc.) to the successor terms.
      - Budget-zero vertices: use the original config term (base case
        of the recursion).

      The traversal is well-founded because k decreases on progress
      edges (trace_rank_strict_on_progress) and never increases
      (trace_rank_monotone).  Since k ∈ [0, B], the recursion
      terminates.

      NOTE: This theorem statement is a roadmap.  The full construction
      requires graph-walking code that is not yet mechanised.
  *)
  Theorem backlink_admissible :
    forall (scb : SC.cfg_builder)
           (Hclosed : SC.builder_succ_closed scb)
           (Hok : SC.trace_condition_ok scb = true)
           (root : nat) (t : Term.Syntax.tm),
      SC.lookup_label scb root = Some (C.jTy [] t (tVar 0)) ->
      exists t_standard,
        unfolds_to scb (lifted_graph scb Hclosed) (root, size (dom scb.(SC.cb_label))) t_standard.
  Proof.
    intros scb Hclosed Hok root t Hlabel.
    set (Gtrace := lifted_graph scb Hclosed).
    set (k0 := size (dom scb.(SC.cb_label))).
    (* The lifted graph is acyclic: the ranking function (snd) strictly
       decreases on progress edges and is monotone on all edges. *)
    assert (Hacyclic : forall xs, FiniteDigraph.is_cycle Gtrace xs -> False).
    { intro xs. intro Hcyc.
      (* Every cycle must contain a progress edge, which decreases k.
         After traversing the cycle, k must be strictly smaller than itself. *)
  Admitted.
