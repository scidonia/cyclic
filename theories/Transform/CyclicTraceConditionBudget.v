From Stdlib Require Import List Arith Lia Utf8 Relations Relation_Operators.
From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Progress Require Import Ranking.


(** Stdpp-compatible wrappers bridging [elem_of] and Coq List [In]. *)

Lemma elem_of_in_map_iff {A B} (f : A -> B) (l : list A) (y : B) :
  y ∈ map f l ↔ ∃ x, f x = y ∧ x ∈ l.
Proof.
  split; intro H.
  - apply elem_of_list_In in H.
    apply (proj1 (@in_map_iff A B f l y)) in H.
    destruct H as [x [Heq Hx]].
    exists x; split; [exact Heq|].
    apply elem_of_list_In, Hx.
  - destruct H as [x [Heq Hx]].
    apply elem_of_list_In in Hx.
    apply (proj2 (elem_of_list_In _ _)).
    apply (proj2 (@in_map_iff A B f l y)).
    exists x; split; [exact Heq|exact Hx].
Qed.

Lemma elem_of_in_prod {A B} (l : list A) (l' : list B) (x : A) (y : B) :
  x ∈ l → y ∈ l' → (x, y) ∈ list_prod l l'.
Proof.
  intros Hx Hy.
  apply elem_of_list_In in Hx. apply elem_of_list_In in Hy.
  apply (proj2 (elem_of_list_In _ _)).
  apply in_prod; assumption.
Qed.

Lemma elem_of_in_prod_iff {A B} (l : list A) (l' : list B) (x : A) (y : B) :
  (x, y) ∈ list_prod l l' ↔ x ∈ l ∧ y ∈ l'.
Proof.
  split; intro H.
  - apply elem_of_list_In in H.
    apply (proj1 (@in_prod_iff A B l l' x y)) in H.
    destruct H. split; apply elem_of_list_In; assumption.
  - destruct H as [Hx Hy].
    apply elem_of_in_prod; assumption.
Qed.

Lemma succ_in_verts (G : FiniteDigraph.fin_digraph) (v w : nat) :
  v ∈ FiniteDigraph.verts G → w ∈ FiniteDigraph.succ G v →
  w ∈ FiniteDigraph.verts G.
Proof.
  intros Hv Hw.
  destruct G as [verts_G succ_G closed_G]; simpl in *.
  apply closed_G in Hv. eapply Forall_forall in Hv; [exact Hv|exact Hw].
Qed.


Import ListNotations.

Set Default Proof Using "Type".

(** A budget-based trace condition.

    This file provides a mechanically provable ranking decrease witness without
    relying on semantic subterm relations.

    Construction:
    - Base graph vertices: [v]
    - Trace graph vertices: [(v,k)] where [k] is a natural-number budget.
    - Non-progress edges preserve the budget.
    - Progress edges consume one unit of budget.

    If the base graph satisfies the global property "every directed cycle
    contains a progress edge", then the trace graph is acyclic (since budgets
    strictly decrease on progress edges and never increase otherwise).

    We therefore obtain a full [Ranking.ranking_condition] witness over nat.
*)

Section BudgetTrace.
  Context (G : @FiniteDigraph.fin_digraph nat _ _).
  Context (is_progress : nat -> bool).

  Definition progress_edge_base (v w : nat) : Prop :=
    is_progress v = true.

  Context (B : nat).

  Fixpoint has_progress_edge_from_base (v : nat) (xs : list nat) : Prop :=
    match xs with
    | [] => False
    | w :: xs' => progress_edge_base v w ∨ has_progress_edge_from_base w xs'
    end.

  Definition has_progress_edge_base (xs : list nat) : Prop :=
    match xs with
    | [] => False
    | v :: xs' => has_progress_edge_from_base v xs'
    end.

  Lemma has_progress_edge_base_cons (v : nat) (xs : list nat) :
    has_progress_edge_base (v :: xs) ↔ has_progress_edge_from_base v xs.
  Proof. simpl. tauto. Qed.

  Lemma has_progress_edge_from_base_cons (v w : nat) (xs : list nat) :
    has_progress_edge_from_base v (w :: xs) ↔
    progress_edge_base v w ∨ has_progress_edge_from_base w xs.
  Proof. simpl. tauto. Qed.

  Definition traceV : Type := nat * nat.

  (** Enumerate trace vertices as a finite set. *)
  Definition trace_verts : gset traceV :=
    list_to_set (list_prod (elements (FiniteDigraph.verts G)) (seq 0 (S B))).

  Lemma trace_vert_inv (v k : nat) :
    (v, k) ∈ trace_verts ->
    v ∈ FiniteDigraph.verts G /\ k <= B.
  Proof.
    intro Hin.
    unfold trace_verts in Hin.
    apply elem_of_list_to_set in Hin.
    apply elem_of_in_prod_iff in Hin.
    destruct Hin as [Hv Hk].
    split.
    - apply elem_of_elements. exact Hv.
    - apply elem_of_list_In in Hk. apply in_seq in Hk. lia.
  Qed.

  Definition trace_succ (vk : traceV) : list traceV :=
    let '(v,k) := vk in
    if is_progress v then
      match k with
      | 0 => []
      | S k' => map (fun w => (w, k')) (FiniteDigraph.succ G v)
      end
    else
      map (fun w => (w, k)) (FiniteDigraph.succ G v).

  Lemma trace_succ_closed :
    forall vk,
      vk ∈ trace_verts ->
      Forall (fun wk => wk ∈ trace_verts) (trace_succ vk).
  Proof.
    intros [v k] Hvk.
    destruct (trace_vert_inv v k Hvk) as [Hv Hk].
    unfold trace_succ.
    destruct (is_progress v) eqn:Hprog.
    - destruct k as [|k'].
      + constructor.
      + apply Forall_forall.
        intros [w kk] Hw.
        apply elem_of_in_map_iff in Hw.
        destruct Hw as [w0 [Hpair Hw0]].
        simpl in Hpair; inversion Hpair; subst.
        apply elem_of_list_to_set.
        apply elem_of_in_prod.
        * apply elem_of_elements.
          exact (succ_in_verts G v w Hv Hw0).
        * apply (proj2 (elem_of_list_In _ _)). apply in_seq. lia.
    - apply Forall_forall.
      intros [w kk] Hw.
      apply elem_of_in_map_iff in Hw.
      destruct Hw as [w0 [Hpair Hw0]].
      simpl in Hpair; inversion Hpair; subst.
      apply elem_of_list_to_set.
      apply elem_of_in_prod.
      + apply elem_of_elements.
        exact (succ_in_verts G v w Hv Hw0).
      + apply (proj2 (elem_of_list_In _ _)). apply in_seq. lia.
  Qed.

  Instance traceV_countable : Countable traceV := _.

  Definition trace_graph : @FiniteDigraph.fin_digraph traceV _ traceV_countable :=
    {| FiniteDigraph.verts := trace_verts;
       FiniteDigraph.succ := trace_succ;
       FiniteDigraph.succ_closed := trace_succ_closed |}.

  (** Progress edges in the trace graph are exactly the edges whose source is
      progress and whose budget strictly decreases. *)
  Definition progress_edge_trace (vk wk : traceV) : Prop :=
    let '(v,k) := vk in
    let '(_,k') := wk in
    is_progress v = true /\ k' < k.

  Definition rank_trace (vk : traceV) : nat := snd vk.

  Lemma not_elem_of_nil {A} (x : A) : x ∉ [].
Proof. intros H; inversion H. Qed.

Lemma trace_edge_budget_le (vk wk : traceV) :
    @FiniteDigraph.edge traceV _ _ trace_graph vk wk ->
    rank_trace wk <= rank_trace vk.
  Proof.
    intros [_Hvin Hwk].
    destruct vk as [v k], wk as [w k'].
    unfold rank_trace. simpl.
    destruct (is_progress v) eqn:Hprog.
    - unfold trace_succ in Hwk. simpl in Hwk. rewrite Hprog in Hwk. simpl in Hwk.
      destruct k as [|k0]; [ inversion Hwk |].
      apply elem_of_in_map_iff in Hwk.
      destruct Hwk as [w0 [Hpair _]].
      simpl in Hpair; inversion Hpair; subst.
      lia.
    - unfold trace_succ in Hwk. simpl in Hwk. rewrite Hprog in Hwk. simpl in Hwk.
      apply elem_of_in_map_iff in Hwk.
      destruct Hwk as [w0 [Hpair _]].
      simpl in Hpair; inversion Hpair; subst.
      lia.
  Qed.

  Lemma trace_edge_budget_lt_on_progress (vk wk : traceV) :
    @FiniteDigraph.edge traceV _ _ trace_graph vk wk ->
    progress_edge_trace vk wk ->
    rank_trace wk < rank_trace vk.
  Proof.
    intros _Hedge Hprog.
    destruct vk as [v k], wk as [w k'].
    unfold progress_edge_trace in Hprog. simpl in Hprog.
    destruct Hprog as [_ Hlt]. exact Hlt.
  Qed.

  Lemma rank_monotone_trace :
    ∀ vk wk, @FiniteDigraph.edge traceV _ _ trace_graph vk wk ->
    clos_refl nat lt (rank_trace wk) (rank_trace vk).
  Proof.
    intros vk wk Hedge.
    destruct (Nat.eq_dec (rank_trace wk) (rank_trace vk)) as [Heq|Hneq].
    - rewrite Heq. apply r_refl.
    - apply r_step.
      pose proof (trace_edge_budget_le vk wk Hedge) as Hle.
      lia.
  Qed.

  Lemma rank_strict_on_progress_trace :
    ∀ vk wk, @FiniteDigraph.edge traceV _ _ trace_graph vk wk ->
    progress_edge_trace vk wk ->
    lt (rank_trace wk) (rank_trace vk).
  Proof.
    intros vk wk Hedge Hprog.
    exact (trace_edge_budget_lt_on_progress vk wk Hedge Hprog).
  Qed.

  (** A trace path projects to a base path by forgetting budgets. *)
  Lemma trace_edges_from_project :
    forall (v : nat) (k : nat) (xs : list traceV),
      @FiniteDigraph.edges_from traceV _ _ trace_graph (v,k) xs ->
      @FiniteDigraph.edges_from nat _ _ G v (map fst xs).
  Proof.
    intros v k xs.
    revert v k.
    induction xs as [|[w k'] xs IH]; cbn; intros v k Hed.
    - exact I.
    - destruct Hed as [Hwk Hed'].
      split.
      + (* show w ∈ succ G v *)
        unfold trace_succ in Hwk.
        destruct (is_progress v) eqn:Hprog.
        * destruct k as [|k0].
           { simpl in Hwk. inversion Hwk. }
          simpl in Hwk.
          apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair Hw0]].
          simpl in Hpair; injection Hpair as -> ->.
          exact Hw0.
        * simpl in Hwk.
          apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair Hw0]].
          simpl in Hpair; injection Hpair as -> ->.
          exact Hw0.
      + apply (IH w k' Hed').
  Qed.

  Lemma trace_is_path_projects :
    forall xs,
      @FiniteDigraph.is_path traceV _ _ trace_graph xs ->
      @FiniteDigraph.is_path nat _ _ G (map fst xs).
  Proof.
    intros xs [Hverts Hedges].
    split.
    - apply Forall_forall.
      intros v Hv.
      apply elem_of_in_map_iff in Hv.
       destruct Hv as [[v0 k0] [Heq Hin]].
       simpl in Heq. subst.
        apply Forall_forall with (x := (v, k0)) in Hverts; [|exact Hin].
        apply trace_vert_inv in Hverts as [Hv_verts _].
        exact Hv_verts.
    - destruct xs as [|[v0 k0] xs']; simpl in Hedges.
      + exact I.
      + exact (trace_edges_from_project v0 k0 xs' Hedges).
  Qed.

  Lemma trace_cycle_projects :
    forall xs,
      @FiniteDigraph.is_cycle traceV _ _ trace_graph xs ->
      @FiniteDigraph.is_cycle nat _ _ G (map fst xs).
  Proof.
    intros xs [vk [ys [Hxs [Hne Hpath]]]].
    destruct vk as [v k].
    exists v, (map fst ys).
    split.
    - rewrite Hxs.
      simpl.
      rewrite map_app.
      simpl.
      reflexivity.
    - split.
      + intro Hnil.
        apply Hne.
        apply map_eq_nil in Hnil.
        exact Hnil.
      + apply trace_is_path_projects.
        exact Hpath.
  Qed.

  (** The last budget in an edges_from chain is <= the starting budget. *)
  Lemma rank_nonincreasing_edges_from (v0 : nat) (k0 : nat) (xs : list traceV) :
    @FiniteDigraph.edges_from traceV _ _ trace_graph (v0, k0) xs ->
    forall vlast klast,
      FiniteDigraph.last_error traceV xs = Some (vlast, klast) ->
      klast <= k0.
  Proof.
    revert v0 k0.
    induction xs as [|[w k'] xs IH]; intros v0 k0 Hedges vlast klast Hlast.
    - simpl in Hlast. discriminate.
     - simpl in Hedges. destruct Hedges as [Hwk Hrest].
       assert (Hk'_le : k' <= k0).
      {
        unfold trace_succ in Hwk.
        destruct (is_progress v0).
        - destruct k0 as [|k0']; [simpl in Hwk; inversion Hwk|].
          simpl in Hwk. apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair _]]. simpl in Hpair; inversion Hpair; subst. lia.
        - simpl in Hwk. apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair _]]. simpl in Hpair; inversion Hpair; subst. lia.
      }
      destruct xs as [|x2 xs'].
      + simpl in Hlast. injection Hlast as <- <-. exact Hk'_le.
      + simpl in Hlast.
        specialize (IH w k' Hrest vlast klast Hlast).
        lia.
  Qed.

  (** A progress edge in the base path lifts to a strict budget decrease. *)
  Lemma progress_edge_gives_strict_decrease (v0 : nat) (k0 : nat) (xs : list traceV) :
    @FiniteDigraph.edges_from traceV _ _ trace_graph (v0, k0) xs ->
    has_progress_edge_base (v0 :: map fst xs) ->
    forall vlast klast,
      FiniteDigraph.last_error traceV xs = Some (vlast, klast) ->
      klast < k0.
  Proof.
    revert v0 k0.
    induction xs as [|[w k'] xs IH]; intros v0 k0 Hedges Hprog vlast klast Hlast.
    - simpl in Hlast. discriminate.
    - simpl in Hedges. destruct Hedges as [Hwk Hrest].
      assert (Hk'_le : k' <= k0).
      {
        unfold trace_succ in Hwk.
        destruct (is_progress v0).
        - destruct k0 as [|k0']; [simpl in Hwk; inversion Hwk|].
          simpl in Hwk. apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair _]]. simpl in Hpair; inversion Hpair; subst. lia.
        - simpl in Hwk. apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair _]]. simpl in Hpair; inversion Hpair; subst. lia.
      }
        (* does the progress edge come at (v0, w) or later? *)
        unfold has_progress_edge_base, has_progress_edge_from_base in Hprog.
        cbn in Hprog.
        destruct Hprog as [Hhead | Htail].
      + (* progress at v0 → w: budget strictly decreases *)
        unfold progress_edge_base in Hhead.
        assert (Hk'_lt : k' < k0).
        {
          unfold trace_succ in Hwk.
          rewrite Hhead in Hwk.
          destruct k0 as [|k0']; [simpl in Hwk; inversion Hwk|].
          simpl in Hwk. apply elem_of_in_map_iff in Hwk.
          destruct Hwk as [w0 [Hpair _]]. simpl in Hpair; inversion Hpair; subst. lia.
        }
        destruct xs as [|x2 xs'].
        * simpl in Hlast. injection Hlast as <- <-. exact Hk'_lt.
        * simpl in Hlast.
          pose proof (rank_nonincreasing_edges_from w k' (x2 :: xs') Hrest vlast klast Hlast).
          lia.
      + (* progress somewhere later *)
        destruct xs as [|x2 xs'].
        * simpl in Hlast. injection Hlast as <- <-.
           simpl in Htail. destruct Htail.
        * simpl in Hlast.
           assert (Hlt : klast < k').
           {
             apply IH with (v0 := w) (k0 := k') (vlast := vlast) (klast := klast);
               [exact Hrest | | exact Hlast].
             unfold has_progress_edge_base; simpl. exact Htail.
          }
          lia.
  Qed.

  (** If the base graph has the cycle-progress property, then the trace graph has no cycles. *)
  Lemma trace_graph_has_no_cycles :
    (forall xs, @FiniteDigraph.is_cycle nat _ _ G xs -> has_progress_edge_base xs) ->
    forall xs, ~ @FiniteDigraph.is_cycle traceV _ _ trace_graph xs.
  Proof.
    intros Hcycle xs Htcyc.
    pose proof (trace_cycle_projects xs Htcyc) as Hbcyc.
    pose proof (Hcycle (map fst xs) Hbcyc) as Hprog.
    (* Unfold the trace cycle: xs = (v0,k0) :: ys ++ [(v0,k0)] *)
    destruct Htcyc as [[v0 k0] [ys [Hxs [Hne Hpath]]]].
    subst xs.
    destruct Hpath as [_Hverts Hedges].
     (* edges_from (v0,k0) (ys ++ [(v0,k0)]) *)
    simpl in Hedges.
    assert (Hlast : FiniteDigraph.last_error traceV (ys ++ [(v0, k0)]) = Some (v0, k0)).
    {
      clear - ys v0 k0.
      induction ys as [|y ys IH]; simpl; [reflexivity|].
      destruct ys as [|y' ys]; simpl; auto.
    }
     assert (Hprog' : has_progress_edge_base (v0 :: map fst (ys ++ [(v0, k0)]))).
    { exact Hprog. }
    pose proof (progress_edge_gives_strict_decrease v0 k0 (ys ++ [(v0, k0)]) Hedges Hprog' v0 k0 Hlast) as Hlt.
    lia.
  Qed.

  Theorem budget_trace_ranking_condition :
    (forall xs, @FiniteDigraph.is_cycle nat _ _ G xs -> has_progress_edge_base xs) ->
    @Ranking.ranking_condition traceV _ _ trace_graph progress_edge_trace nat lt rank_trace.
  Proof.
    intros Hcycle.
    refine {| Ranking.rc_wf := lt_wf;
              Ranking.rc_monotone := rank_monotone_trace;
              Ranking.rc_strict := rank_strict_on_progress_trace;
              Ranking.rc_cycle_progress := _ |}.
    intros xs Hcyc.
    exfalso.
    exact (trace_graph_has_no_cycles Hcycle xs Hcyc).
  Qed.

End BudgetTrace.
