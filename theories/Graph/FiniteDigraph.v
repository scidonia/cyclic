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

  Definition reachable_by_path (G : fin_digraph) (v w : V) : Prop :=
    ∃ xs, is_path_from G v xs ∧ is_path_to G w xs.

  Lemma succ_mem_verts (G : fin_digraph) (v w : V) :
    v ∈ verts G → w ∈ succ G v → w ∈ verts G.
  Proof using EqDecision0 EqDecision1 H V.
    intros Hv Hw.
    pose proof (succ_closed G v Hv) as Hclosed.
    pose proof (Forall_forall (λ x : V, x ∈ verts G) (succ G v)) as Hiff.
    exact ((proj1 Hiff Hclosed) w Hw).
  Qed.

  Lemma reachable_by_path_refl (G : fin_digraph) (v : V) :
    v ∈ verts G → reachable_by_path G v v.
  Proof using EqDecision0 EqDecision1 H V.
    intro Hv.
    exists [v].
    split.
    - split; [reflexivity|].
      split.
      + constructor; [exact Hv|constructor].
      + simpl. exact I.
    - split; [simpl; reflexivity|].
      split.
      + constructor; [exact Hv|constructor].
      + simpl. exact I.
  Qed.

  Lemma reachable_by_path_edge (G : fin_digraph) (v w : V) :
    edge G v w → reachable_by_path G v w.
  Proof using EqDecision0 EqDecision1 H V.
    intros [Hv Hw].
    exists [v; w].
    split.
    - split; [reflexivity|].
      split.
      + constructor.
        * exact Hv.
        * constructor.
          { exact (succ_mem_verts G v w Hv Hw). }
          constructor.
      + simpl. split; [exact Hw|exact I].
    - split; [simpl; reflexivity|].
      split.
      + constructor.
        * exact Hv.
        * constructor.
          { exact (succ_mem_verts G v w Hv Hw). }
          constructor.
      + simpl. split; [exact Hw|exact I].
  Qed.

  Inductive reachable (G : fin_digraph) : V → V → Prop :=
  | reachable_refl v : v ∈ verts G → reachable G v v
  | reachable_step v w u :
      v ∈ verts G →
      w ∈ succ G v →
      reachable G w u →
      reachable G v u.

  Lemma reachable_edge (G : fin_digraph) (v w : V) :
    edge G v w → reachable G v w.
  Proof using EqDecision0 EqDecision1 H V.
    intros [Hv Hw].
    eapply reachable_step; [exact Hv|exact Hw|].
    apply reachable_refl.
    exact (succ_mem_verts G v w Hv Hw).
  Qed.

  Lemma reachable_trans (G : fin_digraph) (v w u : V) :
    reachable G v w → reachable G w u → reachable G v u.
  Proof using EqDecision0 EqDecision1 H V.
    intro Hvw.
    revert u.
    induction Hvw as [v Hv | v x w Hv Hvx Hxw IH]; intros u Hwu.
    - exact Hwu.
    - eapply reachable_step; [exact Hv|exact Hvx|].
      exact (IH u Hwu).
  Qed.

  Definition mut_reachable (G : fin_digraph) (v w : V) : Prop :=
    reachable G v w ∧ reachable G w v.

  Lemma mut_reachable_refl (G : fin_digraph) (v : V) :
    v ∈ verts G → mut_reachable G v v.
  Proof using EqDecision0 EqDecision1 H V.
    intro Hv.
    split; apply reachable_refl; exact Hv.
  Qed.

  Lemma mut_reachable_sym (G : fin_digraph) (v w : V) :
    mut_reachable G v w → mut_reachable G w v.
  Proof using Type.
    intros [Hvw Hwv].
    exact (conj Hwv Hvw).
  Qed.

  Lemma mut_reachable_trans (G : fin_digraph) (u v w : V) :
    mut_reachable G u v → mut_reachable G v w → mut_reachable G u w.
  Proof using EqDecision0 EqDecision1 H V.
    intros [Huv Hvu] [Hvw Hwv].
    split.
    - exact (reachable_trans G u v w Huv Hvw).
    - exact (reachable_trans G w v u Hwv Hvu).
  Qed.

  Definition strongly_connected (G : fin_digraph) (S : gset V) : Prop :=
    (∀ v, v ∈ S → v ∈ verts G) ∧
    (∀ u v, u ∈ S → v ∈ S → mut_reachable G u v).

  Definition is_scc (G : fin_digraph) (S : gset V) : Prop :=
    S ≠ ∅ ∧
    strongly_connected G S ∧
    (∀ T,
      strongly_connected G T →
      S ⊆ T →
      T = S).

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
