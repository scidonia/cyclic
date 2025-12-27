From Stdlib Require Import List Utf8.
From stdpp Require Import prelude countable gmap.

From Cyclic.Graph Require Import FiniteDigraph.

Import ListNotations.

Set Default Proof Using "Type".

Section PreProof.
  Context {Judgement : Type}.
  Context (Rule : Judgement → list Judgement → Prop).

  Context {V : Type} `{EqDecision V} `{Countable V}.

  Record preproof := {
    pp_graph : fin_digraph;
    pp_label : V → Judgement;
    pp_rule_ok : ∀ v,
      v ∈ verts pp_graph →
      Rule (pp_label v) (map pp_label (succ pp_graph v));
  }.

  Record rooted_preproof := {
    rpp_proof : preproof;
    rpp_root : V;
    rpp_root_in : rpp_root ∈ verts rpp_proof.(pp_graph);
  }.
End PreProof.
