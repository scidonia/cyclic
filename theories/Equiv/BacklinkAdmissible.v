From Stdlib Require Import List Bool Arith Lia Utf8.
From stdpp Require Import gmap.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile.
From Cyclic.CyclicProof Require Import Ranked.
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

  (** * Lexicographic ordering for multiple induction parameters

      The budget trace (Claim 2) gives a counter k for each vertex,
      decremented on any progress edge.  We refine this by type:
      per_type_rank(b, I, v) tracks the budget for inductive I.
      The lexicographic product over all I is well-founded. *)

  (** Placeholder: extract the budget counter for vertex v from the
      budget trace construction.  In the mechanised proof, this is
      the second component of the lifted vertex (v, k). *)
  Parameter budget_at_vertex : SC.cfg_builder -> nat -> nat.

  (** For the initial proof, all types share the same counter.
      Later refinement: split by type for individual recursor extraction. *)
  Definition per_type_rank (b : SC.cfg_builder) (I : nat) (v : nat) : nat :=
    budget_at_vertex b v.

  (** Claim 2: the budget counter strictly decreases on progress edges. *)
  Axiom budget_decreases_on_progress :
    forall b v1 v2,
      SC.is_progress_vertex b v1 = true ->
      In v2 (SC.succs_of b v1) ->
      budget_at_vertex b v2 < budget_at_vertex b v1.

  (** Per-type rank decreases on progress edges (trivial from the
      single-counter definition above). *)
  Lemma progress_edge_decreases_rank :
    forall b I v1 v2,
      SC.is_progress_vertex b v1 = true ->
      split_inductive b v1 = Some I ->
      In v2 (SC.succs_of b v1) ->
      per_type_rank b I v2 < per_type_rank b I v1.
  Proof.
    intros b I v1 v2 Hprog Hsplit Hin.
    unfold per_type_rank.
    apply budget_decreases_on_progress; assumption.
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
