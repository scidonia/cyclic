From Stdlib Require Import Utf8 Relations Relation_Operators Wellfounded.
From stdpp Require Import prelude countable.

From Cyclic.Preproof Require Import Preproof.
From Cyclic.Progress Require Import Ranking.
From Cyclic.CyclicProof Require Import CyclicProof.

Set Default Proof Using "Type".

Section RankedCyclicProof.
  Context {Judgement : Type}.
  Context (Rule : Judgement -> list Judgement -> Prop).

  Context {V : Type} `{EqDecision V} `{Countable V}.

  Let preproof := @Preproof.preproof Judgement Rule V _ _.

  (* Progress events can depend on the underlying preproof. *)
  Context (progress_edge : preproof -> V -> V -> Prop).

  Record ranking_witness : Type := {
    rw_M : Type;
    rw_lt : rw_M -> rw_M -> Prop;
    rw_rank : V -> rw_M;
  }.

  Definition progress_ok (p : preproof) (w : ranking_witness) : Prop :=
    @Ranking.ranking_condition V _ _
      (@Preproof.pp_graph Judgement Rule V _ _ p)
      (progress_edge p)
      (rw_M w) (rw_lt w) (rw_rank w).

  Definition cyclic_proof : Type :=
    @CyclicProof.cyclic_proof Judgement Rule V _ _ ranking_witness progress_ok.

  Definition rooted_cyclic_proof : Type :=
    @CyclicProof.rooted_cyclic_proof Judgement Rule V _ _ ranking_witness progress_ok.
End RankedCyclicProof.
