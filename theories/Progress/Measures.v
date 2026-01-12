From Stdlib Require Import Arith Wf_nat Lia Utf8 Relations Relation_Operators Wellfounded.
From stdpp Require Import prelude countable.

From Cyclic.Preproof Require Import Preproof.
From Cyclic.Progress Require Import Ranking.
From Cyclic.CyclicProof Require Import Ranked.

Set Default Proof Using "Type".

Section NatMeasures.
  Context {Judgement : Type}.
  Context (Rule : Judgement -> list Judgement -> Prop).

  Context {V : Type} `{EqDecision V} `{Countable V}.

  Let preproof := @Preproof.preproof Judgement Rule V _ _.

  Context (progress_edge : preproof -> V -> V -> Prop).

  Definition nat_witness (rank : V -> nat)
      : Ranked.ranking_witness (V := V) :=
    {| Ranked.rw_M := nat;
       Ranked.rw_lt := lt;
       Ranked.rw_rank := rank |}.

  Lemma clos_refl_lt_iff_le (a b : nat) :
    clos_refl nat lt a b <-> a <= b.
  Proof.
    split.
    - intro Hab.
      inversion Hab; subst; lia.
    - intro Hab.
      destruct (Nat.eq_dec a b) as [->|Hneq].
      + apply r_refl.
      + assert (Hlt : a < b) by lia.
        eapply r_step.
        exact Hlt.
  Qed.

  Lemma progress_ok_nat (p : preproof) (rank : V -> nat) :
    (forall v w,
        @FiniteDigraph.edge V _ _ (@Preproof.pp_graph Judgement Rule V _ _ p) v w ->
        rank w <= rank v) ->
    (forall v w,
        @FiniteDigraph.edge V _ _ (@Preproof.pp_graph Judgement Rule V _ _ p) v w ->
        progress_edge p v w ->
        rank w < rank v) ->
    (forall xs,
        @FiniteDigraph.is_cycle V _ _ (@Preproof.pp_graph Judgement Rule V _ _ p) xs ->
        @Ranking.has_progress_edge V (progress_edge p) xs) ->
    @Ranked.progress_ok Judgement Rule V _ _ progress_edge p (nat_witness rank).
  Proof.
    intros Hmono Hstrict Hcycle.
    constructor.
    - exact lt_wf.
    - intros v w Hedge.
      apply (proj2 (clos_refl_lt_iff_le _ _)).
      exact (Hmono v w Hedge).
    - intros v w Hedge Hprog.
      exact (Hstrict v w Hedge Hprog).
    - exact Hcycle.
  Qed.
End NatMeasures.
