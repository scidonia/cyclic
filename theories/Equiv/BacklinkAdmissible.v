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

  (** Per-type progress budget. Walks the forward-edges graph from root
      (vertex 0) to v, counting progress edges that split on inductive I. *)
  Fixpoint count_progress_edges
      (b : SC.cfg_builder) (I : nat) (v w : nat) (depth : nat) : option nat :=
    match depth with
    | 0 => None
    | S depth' =>
        if Nat.eqb v w then Some 0
        else
          let succs := SC.succs_of b v in
          let self_progress :=
            if SC.is_progress_vertex b v then
              match SC.lookup_label b v with
              | Some (C.jTy _ (tCase I' (tVar _) _ _) _) =>
                  if Nat.eqb I I' then 1 else 0
              | _ => 0
              end
            else 0
          in
          let fix try_succs (ws : list nat) : option nat :=
            match ws with
            | [] => None
            | w' :: ws' =>
                match count_progress_edges b I w' w depth' with
                | Some n => Some (self_progress + n)
                | None => try_succs ws'
                end
            end
          in
          try_succs succs
    end.

  Definition per_type_rank (b : SC.cfg_builder) (I : nat) (v : nat) : nat :=
    match count_progress_edges b I 0 v (SC.cb_next b) with
    | Some n => n
    | None => SC.cb_next b  (* unreachable — max *)
    end.

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
  Proof.
    intro a.
    (* Well-founded induction on the length of the list *)
    remember (length a) as n.
    revert a Heqn.
    induction n as [|n IH] using (well_founded_induction lt_wf).
    intros a Hlen.
    constructor.
    intros y Hlt.
    inversion Hlt; subst.
    - (* lex_lt_here: same I, smaller rank *)
      apply IH with (y := ((I, r2) :: rs2)).
      + simpl. lia.
      + reflexivity.
    - (* lex_lt_later: same I, same rank, tail decreases *)
      assert (length rs2 < length ((I, r) :: rs2)) by (simpl; lia).
      apply (IH (length rs2) H rs2).
      * reflexivity.
      * exact H0.
  Qed.

  (** If vertex v2 is reachable from v1 by a progress edge splitting on
      inductive I, then per_type_rank I increases by exactly 1, and all
      other types J ≠ I are unchanged.

      This follows from the DFS counting definition of per_type_rank:
      the counter increments by 1 when the progress vertex splitting on
      I is encountered, and by 0 for all other vertices. *)
  Lemma progress_edge_increases_per_type_rank :
    forall b I v1 v2,
      SC.is_progress_vertex b v1 = true ->
      split_inductive b v1 = Some I ->
      In v2 (SC.succs_of b v1) ->
      (* Then per_type_rank I v2 = per_type_rank I v1 + 1 and for J ≠ I,
         per_type_rank J v2 = per_type_rank J v1.
         We state a weaker version: the per-type rank for I strictly increases. *)
      exists p, count_progress_edges b I 0 v2 (SC.cb_next b) = Some p /\
           count_progress_edges b I 0 v1 (SC.cb_next b) = Some (p - 1).
  Proof.
    intros b I v1 v2 Hprog Hsplit Hin.
    (* Admitted: requires reasoning about DFS path uniqueness in the SC graph.
       Follows from the fact that the forward graph is a tree (no cycles
       before generalisation), so the path from root is unique. *)
  Admitted.

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
