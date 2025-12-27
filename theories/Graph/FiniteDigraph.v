From Stdlib Require Import List Utf8.
From stdpp Require Import prelude gmap.

Import ListNotations.

Set Default Proof Using "Type".

Section Digraph.
  Context (V : Type) `{EqDecision V} `{Countable V}.

  Record fin_digraph := {
    verts : gset V;
    succ : V → list V;
    succ_closed : ∀ v, v ∈ verts → Forall (λ w, w ∈ verts) (succ v);
  }.

  Definition edge (G : fin_digraph) (v w : V) : Prop :=
    v ∈ verts G ∧ w ∈ succ G v.

  Definition out_neighbours (G : fin_digraph) (v : V) : list V :=
    succ G v.

  Fixpoint last_error (xs : list V) : option V :=
    match xs with
    | [] => None
    | [x] => Some x
    | _ :: xs' => last_error xs'
    end.

  Fixpoint edges_from (G : fin_digraph) (v : V) (xs : list V) : Prop :=
    match xs with
    | [] => True
    | w :: xs' => w ∈ succ G v ∧ edges_from G w xs'
    end.

  Definition edges_along (G : fin_digraph) (xs : list V) : Prop :=
    match xs with
    | [] => True
    | v :: xs' => edges_from G v xs'
    end.

  Definition is_path (G : fin_digraph) (xs : list V) : Prop :=
    Forall (λ v, v ∈ verts G) xs ∧ edges_along G xs.

  Definition is_path_from (G : fin_digraph) (v : V) (xs : list V) : Prop :=
    hd_error xs = Some v ∧ is_path G xs.

  Definition is_path_to (G : fin_digraph) (v : V) (xs : list V) : Prop :=
    last_error xs = Some v ∧ is_path G xs.

  Definition is_cycle (G : fin_digraph) (xs : list V) : Prop :=
    ∃ v ys,
      xs = v :: ys ++ [v] ∧
      ys ≠ [] ∧
      is_path G xs.

  Lemma edge_iff (G : fin_digraph) (v w : V) :
    edge G v w ↔ v ∈ verts G ∧ w ∈ succ G v.
  Proof.
    unfold edge.
    tauto.
  Qed.
End Digraph.

Arguments fin_digraph {_} {_} {_}.
Arguments verts {_} {_} {_} _.
Arguments succ {_} {_} {_} _ _.
Arguments succ_closed {_} {_} {_} _ _ _.
