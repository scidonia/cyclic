From Coq Require Import List.
From stdpp Require Import base list gmap gset.

Import ListNotations.

Set Default Proof Using "Type".

Record fin_digraph (V : Type) `{EqDecision V} `{Countable V} := {
  verts : gset V;
  succ : V -> list V;
  succ_closed : forall v, v ∈ verts -> Forall (fun w => w ∈ verts) (succ v);
}.

Section Basic.
  Context {V : Type} `{EqDecision V} `{Countable V}.

  Definition edge (G : fin_digraph V) (v w : V) : Prop :=
    v ∈ G.(verts) /\ w ∈ G.(succ) v.

  Definition out_neighbours (G : fin_digraph V) (v : V) : list V :=
    G.(succ) v.
End Basic.
