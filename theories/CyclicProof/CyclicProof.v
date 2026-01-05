From Stdlib Require Import Utf8.
From stdpp Require Import prelude countable.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.

Set Default Proof Using "Type".

Section CyclicProof.
  Context {Judgement : Type}.
  Context (Rule : Judgement -> list Judgement -> Prop).

  Context {V : Type} `{EqDecision V} `{Countable V}.

  Let preproof := @Preproof.preproof Judgement Rule V _ _.

  Context (W : Type).
  Context (progress_ok : preproof -> W -> Prop).

  Record cyclic_proof : Type := {
    cp_preproof : preproof;
    cp_witness : W;
    cp_progress_ok : progress_ok cp_preproof cp_witness;
  }.

  Record rooted_cyclic_proof : Type := {
    rcp_proof : cyclic_proof;
    rcp_root : V;
    rcp_root_in : rcp_root ∈ verts (pp_graph Rule (cp_preproof rcp_proof));
  }.
End CyclicProof.
