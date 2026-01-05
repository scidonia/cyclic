

From Stdlib Require Import List Utf8 Relations Relation_Operators Wellfounded.
From stdpp Require Import prelude countable.

From Cyclic.Graph Require Import FiniteDigraph.

Import ListNotations.

Set Default Proof Using "Type".

Section Ranking.
  Context (V : Type) `{EqDecision V} `{Countable V}.
  Context (G : @fin_digraph V _ _).

  (* A "progress edge" marks where we must strictly decrease. *)
  Context (progress_edge : V -> V -> Prop).

  (* Ranking domain + a well-founded strict order. *)
  Context (M : Type).
  Context (ltM : M -> M -> Prop).

  Definition leM : M -> M -> Prop := clos_refl M ltM.

  Context (rank : V -> M).

  Definition rank_monotone : Prop :=
    ∀ v w, @FiniteDigraph.edge V _ _ G v w -> leM (rank w) (rank v).

  Definition rank_strict_on_progress : Prop :=
    ∀ v w, @FiniteDigraph.edge V _ _ G v w -> progress_edge v w -> ltM (rank w) (rank v).

  Fixpoint has_progress_edge_from (v : V) (xs : list V) : Prop :=
    match xs with
    | [] => False
    | w :: xs' => progress_edge v w ∨ has_progress_edge_from w xs'
    end.

  Definition has_progress_edge (xs : list V) : Prop :=
    match xs with
    | [] => False
    | v :: xs' => has_progress_edge_from v xs'
    end.

  Lemma has_progress_edge_from_cons (v w : V) (xs : list V) :
    has_progress_edge_from v (w :: xs) ↔
      progress_edge v w ∨ has_progress_edge_from w xs.
  Proof using M V ltM progress_edge rank.
    simpl. tauto.
  Qed.

  Lemma has_progress_edge_cons (v : V) (xs : list V) :
    has_progress_edge (v :: xs) ↔ has_progress_edge_from v xs.
  Proof using M V ltM progress_edge rank.
    simpl. tauto.
  Qed.

  Lemma last_error_nonempty (xs : list V) :
    xs ≠ [] -> ∃ u, last_error V xs = Some u.
  Proof using Type.
    induction xs as [|x xs IH]; intro Hne.
    - exfalso. apply Hne. reflexivity.
    - destruct xs as [|y xs'].
      + exists x. reflexivity.
      + assert (Hne' : y :: xs' ≠ []) by discriminate.
        destruct (IH Hne') as [u Hu].
        exists u.
        simpl.
        exact Hu.
  Qed.

  Lemma has_progress_edge_from_app (v : V) (xs ys : list V) :
    has_progress_edge_from v (xs ++ ys) ↔
      has_progress_edge_from v xs ∨
      match last_error V xs with
      | None => has_progress_edge_from v ys
      | Some u => has_progress_edge_from u ys
      end.
  Proof using M V ltM progress_edge rank.
    revert v.
    induction xs as [|x xs IH]; intro v.
    - simpl. tauto.
    - destruct xs as [|x' xs'].
      + simpl. tauto.
      + simpl.
        specialize (IH x).
        assert (Hne : x' :: xs' ≠ []) by discriminate.
        destruct (last_error_nonempty (x' :: xs') Hne) as [u Hu0].
        pose proof Hu0 as Hu.
        simpl in Hu.
        rewrite IH.
        simpl.
        rewrite Hu.
        simpl.
        split.
        * intro Hp.
          destruct Hp as [Hvx|[Hx|Hy]];
            [ left; left; exact Hvx
            | left; right; exact Hx
            | right; exact Hy ].
        * intro Hp.
          destruct Hp as [[Hvx|Hx]|Hy];
            [ left; exact Hvx
            | right; left; exact Hx
            | right; right; exact Hy ].
  Qed.

  (* Ranking-based global condition, parameterized by a chosen progress predicate.
     Intuition: along every edge rank does not increase; on designated progress
     edges it strictly decreases; and every directed cycle has a progress edge. *)
  Record ranking_condition : Prop := {
    rc_wf : well_founded ltM;
    rc_monotone : rank_monotone;
    rc_strict : rank_strict_on_progress;
    rc_cycle_progress : ∀ xs, @FiniteDigraph.is_cycle V _ _ G xs -> has_progress_edge xs;
  }.
End Ranking.
