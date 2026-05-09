From Stdlib Require Import List Bool Arith Lia Utf8.
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

  (** Count progress vertices on inductive I with index < limit. *)
  Fixpoint count_progress_upto (b : SC.cfg_builder) (I limit : nat) : nat :=
    match limit with
    | 0 => 0
    | S limit' =>
        let rec := count_progress_upto b I limit' in
        match split_inductive b limit' with
        | Some I' => if Nat.eqb I I' then S rec else rec
        | None => rec
        end
    end.

  Definition per_type_rank (b : SC.cfg_builder) (I : nat) (v : nat) : nat :=
    let total := count_progress_upto b I (SC.cb_next b) in
    total - count_progress_upto b I v.

  (** Monotonicity: count_progress_upto is non-decreasing in the limit. *)
  Lemma count_upto_mono : forall b I n m,
    n <= m -> count_progress_upto b I n <= count_progress_upto b I m.
  Proof.
    induction 1 as [|m Hle IH].
    - reflexivity.
    - simpl. destruct (split_inductive b m) as [I'|]; try lia.
      destruct (Nat.eqb I I'); lia.
  Qed.

  (** Successor vertices are allocated after their parent. *)
  Lemma succ_gt : forall b v w,
    In w (SC.succs_of b v) -> w > v.
  Proof.
    intros b v w Hin.
    (* The SC allocates vertices sequentially; a successor is
       created after its parent.  This follows from the SC
       construction in Supercompile.v. *)
    (* For now, use cb_next as an upper bound: w < cb_next,
       and the succ list only contains previously-seen vertices
       or newly-allocated ones.  The newly-allocated ones
       are allocated AFTER v. *)
    assert (Hbound : w < SC.cb_next b) by admit.
    (* We need: if w is in succs_of v, then w > v.
       This follows from the memo table invariant. *)
    admit.
  Admitted.

  (** Remaining budget strictly decreases across a progress edge. *)
  Lemma progress_edge_decreases_rank :
    forall b I v1 v2,
      SC.is_progress_vertex b v1 = true ->
      split_inductive b v1 = Some I ->
      In v2 (SC.succs_of b v1) ->
      per_type_rank b I v2 < per_type_rank b I v1.
  Proof.
    intros b I v1 v2 Hprog Hsplit Hin.
    unfold per_type_rank.
    assert (Hgt : v1 < v2) by (apply (succ_gt b v1 v2 Hin)).
    assert (Hmono : count_progress_upto b I v1 < count_progress_upto b I (S v1)).
    { simpl. unfold split_inductive in Hsplit.
      destruct (SC.lookup_label b v1) as [[[]]|] eqn:Hlabel; try discriminate.
      destruct (SC.is_progress_vertex b v1) eqn:Hprog'; try discriminate.
      inversion Hsplit. subst i.
      rewrite Nat.eqb_refl. lia. }
    assert (Hle : count_progress_upto b I (S v1) <= count_progress_upto b I v2).
    { apply count_upto_mono. lia. }
    lia.
  Qed.

  (** Every vertex appears after its parent in allocation order. *)
  Lemma succ_gt : forall b v1 v2,
    In v2 (SC.succs_of b v1) -> v2 > v1.
  Proof.
  Admitted.

  (** If v1 is a progress vertex on I, then per_type_rank I v2 > per_type_rank I v1
      whenever v2 is a successor of v1. *)
  Lemma progress_edge_increases_per_type_rank :
    forall b I v1 v2,
      SC.is_progress_vertex b v1 = true ->
      split_inductive b v1 = Some I ->
      In v2 (SC.succs_of b v1) ->
      per_type_rank b I v2 = per_type_rank b I v1 + 1.
  Proof.
    intros b I v1 v2 Hprog Hsplit Hin.
    unfold per_type_rank.
    pose proof (succ_gt b v1 v2 Hin) as Hgt.
    (* v2 > v1, so seq 0 v2 = seq 0 v1 ++ [v1; ...; v2-1].
       The key: v1 is in seq 0 v2 but NOT in seq 0 v1. *)
    rewrite (seq_app 0 v1 v2) by lia.
    rewrite filter_app, app_length.
    simpl.
    (* Need to show: v1 matches split_inductive.
       From Hsplit: split_inductive b v1 = Some I. *)
    unfold split_inductive in Hsplit.
    destruct (SC.lookup_label b v1) as [[[]]|] eqn:Hlabel; try discriminate.
    destruct (SC.is_progress_vertex b v1) eqn:Hprog'; try discriminate.
    inversion Hsplit. subst i.
    assert (Heq : (fun w : nat =>
      match split_inductive b w with
      | Some I' => Nat.eqb I I'
      | None => false
      end) v1 = true).
    { unfold split_inductive. rewrite Hlabel, Hprog'.
      rewrite Nat.eqb_refl. reflexivity. }
    (* Now we need a lemma: if a predicate P holds at element x,
       then filter P (seq a (b-a)) includes x exactly once. *)
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
