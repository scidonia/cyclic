From Coq Require Import List.
From stdpp Require Import base list gset.

From cyclic.theories.Graph Require Import FiniteDigraph.

Import ListNotations.

Set Default Proof Using "Type".

Section PreProof.
  Context {Judgement : Type}.
  Context (Rule : Judgement -> list Judgement -> Prop).

  Context {V : Type} `{EqDecision V} `{Countable V}.

  Record preproof := {
    pp_graph : fin_digraph V;
    pp_label : V -> Judgement;
    pp_rule_ok : forall v,
      v ∈ pp_graph.(verts) ->
      Rule (pp_label v) (map pp_label (pp_graph.(succ) v));
  }.

  Record rooted_preproof := {
    rpp_proof : preproof;
    rpp_root : V;
    rpp_root_in : rpp_root ∈ rpp_proof.(pp_graph).(verts);
  }.
End PreProof.
