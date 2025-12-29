From Stdlib Require Import List Utf8.
From stdpp Require Import prelude countable.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.

Import ListNotations.

Set Default Proof Using "Type".

Section Bisimulation.
  Context {Judgement : Type}.
  Context (Rule : Judgement -> list Judgement -> Prop).

  Section TwoGraphs.
    Context {V1 : Type} `{EqDecision V1} `{Countable V1}.
    Context {V2 : Type} `{EqDecision V2} `{Countable V2}.

    Let preproof1 := @preproof Judgement Rule V1 _ _.
    Let preproof2 := @preproof Judgement Rule V2 _ _.

    Definition rel := V1 -> V2 -> Prop.

    Definition pp_graph1 (p : preproof1) : FiniteDigraph.fin_digraph :=
      @pp_graph Judgement Rule V1 _ _ p.

    Definition pp_graph2 (p : preproof2) : FiniteDigraph.fin_digraph :=
      @pp_graph Judgement Rule V2 _ _ p.

    Definition pp_label1 (p : preproof1) (v : V1) : Judgement :=
      @pp_label Judgement Rule V1 _ _ p v.

    Definition pp_label2 (p : preproof2) (v : V2) : Judgement :=
      @pp_label Judgement Rule V2 _ _ p v.

    Definition pp_edge1 (p : preproof1) (v w : V1) : Prop :=
      @FiniteDigraph.edge V1 _ _ (pp_graph1 p) v w.

    Definition pp_edge2 (p : preproof2) (v w : V2) : Prop :=
      @FiniteDigraph.edge V2 _ _ (pp_graph2 p) v w.

    Record bisimulation (p : preproof1) (q : preproof2) (R : rel) : Prop := {
      bisim_verts :
        ∀ v w, R v w →
          v ∈ verts (pp_graph1 p) ∧ w ∈ verts (pp_graph2 q);

      bisim_label :
        ∀ v w, R v w →
          pp_label1 p v = pp_label2 q w;

      bisim_forth :
        ∀ v w v', R v w →
          pp_edge1 p v v' →
          ∃ w', pp_edge2 q w w' ∧ R v' w';

      bisim_back :
        ∀ v w w', R v w →
          pp_edge2 q w w' →
          ∃ v', pp_edge1 p v v' ∧ R v' w';
    }.

    Definition flip_rel (R : rel) : V2 -> V1 -> Prop :=
      fun w v => R v w.

    Definition rooted_bisimilar
        (p : @rooted_preproof Judgement Rule V1 _ _)
        (q : @rooted_preproof Judgement Rule V2 _ _) : Prop :=
      ∃ R,
        bisimulation (@rpp_proof Judgement Rule V1 _ _ p) (@rpp_proof Judgement Rule V2 _ _ q) R ∧
        R (@rpp_root Judgement Rule V1 _ _ p) (@rpp_root Judgement Rule V2 _ _ q).
  End TwoGraphs.
End Bisimulation.
