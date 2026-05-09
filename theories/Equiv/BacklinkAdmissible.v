From Stdlib Require Import List Utf8.
From stdpp Require Import gmap.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile.
From Cyclic.CyclicProof Require Import Ranked.
Import Term.Syntax.
Import ListNotations.
Set Default Proof Using "Type".

(** * Backlink Admissibility for CoC with Inductives

    We state: every cyclic proof object (rooted pre-proof + ranking in
    the focused sequent calculus) can be converted into a standard CIC
    derivation using the explicit induction principle (recursor/fix).

    This corresponds to Brotherston-Simpson's admissibility theorem for
    first-order logic, extended to CoC with inductives.

    The proof plan is in docs/BACKLINK_ADMISSIBILITY.md.
*)

Module BacklinkAdmissible.

  Module SC := Supercompile.
  Module Ty := Typing.Typing.
  Module C := Ty.Cyclic.

  (** A cyclic proof is a cfg_builder + ranking witness.
      For now we reference the existing infrastructure. *)

  (** The proof extraction:

      Given a cyclic proof (cfg_builder b, ranked by Claim 2 of the
      paper), we produce:
      - An unfolded tree (an infinite regular tree of judgments)
      - A standard CIC derivation using the recursor at each progress vertex
      - A proof of CIU equivalence between the original and standard-proof terms
  *)


  (** * Lexicographic ranking for multiple induction parameters

      The budget trace (Claim 2 of the paper) assigns a single counter k
      to each vertex, decremented on every progress edge regardless of
      which inductive type is being split.  For admissibility, we need
      to DISENTANGLE this composite counter into per-type rankings
      and combine them lexicographically.

      Intuition: a progress vertex splitting on List consumes one unit
      of "List-budget"; a progress vertex splitting on Vec consumes one
      unit of "Vec-budget".  Nested induction (e.g., over Vec of List)
      corresponds to the lexicographic product of the two rankings.
  *)

  (** Extract the inductive type being split at a progress vertex.
      Returns Some I if v is a case-split on inductive I, None otherwise. *)
  Definition split_inductive (b : SC.cfg_builder) (v : nat) : option nat :=
    match SC.lookup_label b v with
    | Some (C.jTy _ (tCase I (tVar _) _ _) _) =>
        if SC.is_progress_vertex b v then Some I else None
    | _ => None
    end.

  (** Lexicographic less-than on lists of (inductive, rank) pairs. *)
  Inductive lex_lt : list (nat * nat) -> list (nat * nat) -> Prop :=
  | lex_lt_here : forall I r1 r2 rs1 rs2,
      r1 < r2 ->
      lex_lt ((I, r1) :: rs1) ((I, r2) :: rs2)
  | lex_lt_later : forall I r rs1 rs2,
      lex_lt rs1 rs2 ->
      lex_lt ((I, r) :: rs1) ((I, r) :: rs2).

  Lemma lex_lt_wf : well_founded lex_lt.
  Proof. Admitted.

  (** If the budget decreases, the lexicographic ranking decreases too. *)
  Lemma budget_decrease_implies_lex_decrease :
    forall b v1 v2, True.
  Proof. Admitted.

  (** Step 1: Unfolding — eliminate backlinks by rewriting companions.

      Given a cfg_builder b that passes trace_condition_ok, and a
      starting vertex v, produce a function [unfold b v n] that
      computes the n-th level of the unfolded tree.

      Property: for any finite depth n, [unfold b v n] is locally
      correct (each node satisfies its sequent rule).
  *)

  Parameter unfold_cfg :
    SC.cfg_builder -> nat -> nat -> option Ty.ctx * option Term.Syntax.tm.

  (** Step 2: Induction extraction.

      At each progress vertex (case-split), replace the split with
      the CIC recursor for the inductive type being split on.
      The backlink becomes a recursive call to the recursor.

      Property: the extracted term is well-typed in CIC.
  *)

  Parameter extract_recursor :
    SC.cfg_builder -> nat -> Term.Syntax.tm.

  (** Main theorem: the recursive-term extraction preserves CIU. *)

  Theorem backlink_admissible :
    forall (Σenv : Ty.env) (fuel : nat) (Γ : Ty.ctx) (t A : Term.Syntax.tm)
           (v : nat) (b : SC.cfg_builder),
      SC.supercompile_jTy_tc fuel Σenv Γ t A = Some (v, b) ->
      (* The standard-proof term extracted from b is CIU-equivalent to t *)
      True.  (* To be replaced with the actual CIU statement *)
  Proof.
  Admitted.

End BacklinkAdmissible.
