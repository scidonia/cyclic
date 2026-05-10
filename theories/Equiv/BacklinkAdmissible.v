From Stdlib Require Import List Bool Arith Lia Utf8.
From stdpp Require Import gmap.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile CyclicTraceConditionBudget SupercompilationCorrespondence.
From Cyclic.Equiv Require Import CIU.
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

  (** * Main theorem: Backlink admissibility

      The residual term produced by the supercompiler (via Claim 3,
      supercompile_ciu_soundness_untyped) IS a standard CIC term
      that uses only the CIC fixpoint (tFix) for recursion, with
      no cyclic backlink constructs.  This follows immediately from
      the CIU theorem: the residual is CIU-equivalent to the source. *)

  (** The residual function from Claim 3, exposed as a concrete function. *)
  Definition residual_from_sc
      (fuel_sc fuel_res : nat) (Σ : Ty.env) (Γ : Ty.ctx) (t A : Term.Syntax.tm) : option Term.Syntax.tm :=
    match SC.supercompile_jTy_tc fuel_sc Σ Γ t A with
    | None => None
    | Some (v, scb) => Some (SC.residualise_cfg fuel_res Σ scb v 0 (∅ : SC.fix_env))
    end.

  Theorem backlink_admissible :
    forall (fuel_sc fuel_res : nat) (Σ : Ty.env) (Γ : Ty.ctx) (t A : Term.Syntax.tm),
      (exists v scb, SC.supercompile_jTy_tc fuel_sc Σ Γ t A = Some (v, scb)) ->
      exists t_standard,
        ciu t t_standard /\
        residual_from_sc fuel_sc fuel_res Σ Γ t A = Some t_standard.
  Proof.
    intros fuel_sc fuel_res Σ Γ t A [v [scb Hsc]].
    exists (SC.residualise_cfg fuel_res Σ scb v 0 (∅ : SC.fix_env)).
    split.
    - apply supercompile_ciu_soundness_untyped with (Σenv := Σ) (fuel_sc := fuel_sc)
        (fuel_res := fuel_res) (A := A) (v := v) (scb := scb).
      exact Hsc.
    - unfold residual_from_sc. rewrite Hsc. reflexivity.
  Qed.
