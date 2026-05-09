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
    intros y Hlt.
    inversion Hlt; subst.
    - apply IH with (y := ((I, r2) :: rs2)).
      + simpl. lia.
      + reflexivity.
    - assert (length rs2 < length ((I, r) :: rs2)) by (simpl; lia).
      apply (IH (length rs2) H rs2).
      * reflexivity.
      * exact H0.
  Qed.

  (** Build the lexicographic ranking from per-type ranks.
      For now, a single-element list (degenerate lexicographic). *)
  Definition lex_ranking (b : SC.cfg_builder) (v : nat) : list (nat * nat) :=
    [(0, per_type_rank b 0 v)].

  (** The composite ranking is well-founded because the budget
      decreases on each progress edge. *)
  Lemma ranking_decreases_on_progress :
    forall b v1 v2,
      SC.is_progress_vertex b v1 = true ->
      In v2 (SC.succs_of b v1) ->
      lex_lt (lex_ranking b v1) (lex_ranking b v2).
  Proof.
    intros b v1 v2 Hprog Hin.
    unfold lex_ranking.
    apply lex_lt_here.
    unfold per_type_rank.
    apply budget_decreases_on_progress; assumption.
  Qed.

  (** * Main theorem (placeholder) *)
  Theorem backlink_admissible :
    forall (Σenv : Ty.env) (fuel : nat) (Γ : Ty.ctx) (t A : Term.Syntax.tm)
           (v : nat) (b : SC.cfg_builder),
      SC.supercompile_jTy_tc fuel Σenv Γ t A = Some (v, b) ->
      True.
  Proof.
  Admitted.

End BacklinkAdmissible.
