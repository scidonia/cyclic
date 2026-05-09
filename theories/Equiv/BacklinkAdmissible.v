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

  (** Base case: count from a vertex to itself is zero. *)
  Lemma count_refl : forall b I v depth,
    count_progress_edges b I v v depth = Some 0.
  Proof.
    intros. destruct depth; simpl; rewrite Nat.eqb_refl; reflexivity.
  Qed.

  (** try_succs: if w is in the successor list, the recursive call
      for w determines the result. *)
  Lemma try_succs_in :
    forall (b : SC.cfg_builder) (I : nat) (target : nat)
           (succs : list nat) (w : nat) (depth : nat) (n : nat),
      In w succs ->
      count_progress_edges b I w target depth = Some n ->
      (fix try_succs (ws : list nat) : option nat :=
         match ws with
         | [] => None
         | w' :: ws' =>
             match count_progress_edges b I w' target depth with
             | Some n0 => Some n0
             | None => try_succs ws'
             end
         end) succs = Some n.
  Proof.
    induction succs as [|x xs IH]; intros w depth n Hin Hcount.
    - inversion Hin.
    - simpl in Hin. destruct Hin as [->|Hin'].
      + simpl. rewrite Hcount. reflexivity.
      + simpl. destruct (count_progress_edges b I x target depth) as [n0|] eqn:Hc.
        * reflexivity.
        * apply (IH xs w depth n Hin' Hcount).
  Qed.

  (** Single step: if v1 is a progress vertex on I and v2 is a successor,
      then count(v1 → v2) = Some 1. *)
  Lemma progress_edge_increases_count :
    forall b I v1 v2 depth,
      depth > 0 ->
      SC.is_progress_vertex b v1 = true ->
      split_inductive b v1 = Some I ->
      In v2 (SC.succs_of b v1) ->
      count_progress_edges b I v1 v2 depth = Some 1.
  Proof.
    intros b I v1 v2 depth Hdepth Hprog Hsplit Hin.
    unfold split_inductive in Hsplit.
    destruct (SC.lookup_label b v1) as [[[]]|] eqn:Hlabel; try discriminate.
    (* It's a jTy *)
    destruct (SC.is_progress_vertex b v1) eqn:Hprog'; try discriminate.
    inversion Hsplit. subst i.
    destruct depth as [|depth']; [lia|].
    simpl. rewrite Hprog'. rewrite Hlabel. simpl.
    rewrite Nat.eqb_refl. simpl.
    eapply try_succs_in.
    - exact Hin.
    - apply count_refl.
  Qed.

  (** If v2 is a successor of v1 which is a progress vertex on I,
      then the count to v2 equals the count to v1 plus 1. *)
  Lemma progress_edge_increases_count :
    forall b I v1 v2 depth,
      SC.is_progress_vertex b v1 = true ->
      match SC.lookup_label b v1 with
      | Some (C.jTy _ (tCase I' (tVar _) _ _) _) => Nat.eqb I I' = true
      | _ => False
      end ->
      In v2 (SC.succs_of b v1) ->
      count_progress_edges b I v1 v2 depth = Some 1.
  Proof.
    intros b I v1 v2 depth Hprog Hmatch Hin.
    simpl.
    rewrite Hprog.
    destruct (SC.lookup_label b v1) as [[[]| |]|] eqn:Hlabel; try contradiction.
    (* It's a jTy with tCase *)
    destruct Hmatch as [Hmatch'|].
    - (* The inductive matches *)
      rewrite (Nat.eqb_eq _ _ Hmatch').
      simpl.
      (* We get self_progress = 1, try successors, v2 is in the list *)
      admit.
    - contradiction.
  Admitted.

  (** Main lemma: per_type_rank increases by 1 across a progress edge. *)
  Lemma progress_edge_increases_per_type_rank :
    forall b I v1 v2,
      SC.is_progress_vertex b v1 = true ->
      split_inductive b v1 = Some I ->
      In v2 (SC.succs_of b v1) ->
      per_type_rank b I v2 = per_type_rank b I v1 + 1.
  Proof.
    intros b I v1 v2 Hprog Hsplit Hin.
    unfold per_type_rank.
    set (depth := SC.cb_next b).
    (* Both counts exist because cb_next bounds the graph depth. *)
    assert (Hdepth : depth > 0).
    { unfold depth. pose proof (SC.cb_next b). lia. }
    pose proof (progress_edge_increases_count b I v1 v2 depth Hdepth Hprog Hsplit Hin) as Hinc.
    destruct (count_progress_edges b I 0 v2 depth) as [c2|] eqn:Hc2;
      destruct (count_progress_edges b I 0 v1 depth) as [c1|] eqn:Hc1.
    (* Need to relate c2 to c1.  The count to v2 is at least c1 + 1
       because the path to v2 must pass through v1.
       We state a weaker result: since both sides are reachable,
       the counts differ by at least 1. *)
    2,3,4: exfalso; (* unreachable vertices: cb_next bounds graph *)
            admit.
    (* The key insight: the path to v2 MUST go through v1,
       because v2 is a child of v1 in the exploration tree.
       This follows from the SC graph construction:
       vertices are allocated in order, and each vertex (except 0)
       appears in exactly one cb_succ entry.
       Admitted for now. *)
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
