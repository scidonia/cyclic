From Stdlib Require Import List ListDec Bool Arith Lia Utf8.
From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Progress Require Import Ranking.
From Cyclic.Transform Require Import Supercompile.

Import ListNotations.

Set Default Proof Using "Type".

Module SC := Supercompile.

(** Proof-facing soundness statement for the boolean trace-condition check.

    The implementation provides [trace_condition_ok : cfg_builder -> bool],
    intended to reject configuration graphs that contain a directed cycle with
    no progress events.

    This file isolates the hardest global obligation first:

    - every directed cycle contains a progress edge.

    We phrase progress edges using [is_progress_vertex], aligned with
    [Transform/CyclicTraceCondition.v] where progress events are split steps.
*)

Section CycleProgress.

  (** Boolean membership used by the supercompiler. *)
  Lemma mem_nat_true_iff (x : nat) (xs : list nat) :
    SC.mem_nat x xs = true <-> In x xs.
  Proof.
    induction xs as [|y ys IH]; cbn.
    - split; intro H; [discriminate|contradiction].
    - rewrite Bool.orb_true_iff.
      rewrite Nat.eqb_eq.
      rewrite IH.
      split.
      + intros [H|H].
        * subst. left. reflexivity.
        * right. exact H.
      + intros [H|H].
        * left. exact H.
        * right. exact H.
  Qed.

  Lemma mem_nat_false_iff (x : nat) (xs : list nat) :
    SC.mem_nat x xs = false <-> ~ In x xs.
  Proof.
    rewrite <- mem_nat_true_iff.
    destruct (SC.mem_nat x xs); split; congruence.
  Qed.

  Lemma in_nub_nat_iff (x : nat) (xs : list nat) :
    In x (SC.nub_nat xs) <-> In x xs.
  Proof.
    induction xs as [|y ys IH]; cbn.
    - tauto.
    - set (zs := SC.nub_nat ys).
      destruct (existsb (Nat.eqb y) zs) eqn:Hex.
      + rewrite IH. tauto.
      + rewrite IH. simpl. tauto.
  Qed.

  (** A simple, proof-friendly reachability predicate matching [SC.reach_depth].

      [steps_le k b v w] means there is a path from [v] to [w] of length at most
      [k+1] (measured in edges), following [succs_of].
  *)
  Fixpoint steps_le (k : nat) (b : SC.cfg_builder) (v w : nat) : Prop :=
    match k with
    | 0 => In w (SC.succs_of b v)
    | S k' => In w (SC.succs_of b v) \/ exists u, In u (SC.succs_of b v) /\ steps_le k' b u w
    end.

  Lemma in_fold_reach_depth :
    forall k b succs u x,
      In u succs ->
      In x (SC.reach_depth k b u) ->
      In x (fold_right (fun w acc => SC.reach_depth k b w ++ acc) [] succs).
  Proof.
    intros k b succs.
    induction succs as [|w ws IH]; intros u x Hu Hx; [contradiction|].
    simpl in Hu.
    destruct Hu as [->|Hu].
    - simpl. apply in_or_app. left. exact Hx.
    - simpl. apply in_or_app. right.
      apply IH with (u := u); assumption.
  Qed.

  Lemma steps_le_in_reach_depth :
    forall k b v w,
      steps_le k b v w ->
      In w (SC.reach_depth k b v).
  Proof.
    induction k as [|k' IH]; intros b v w H.
    - simpl. exact H.
    - simpl in H.
      simpl.
      apply in_nub_nat_iff.
      destruct H as [H1 | [u [Hu H2]]].
      + apply in_or_app. left. exact H1.
      + apply in_or_app. right.
        eapply in_fold_reach_depth; [exact Hu|].
        exact (IH b u w H2).
  Qed.

  Lemma steps_le_S :
    forall k b v w,
      steps_le k b v w -> steps_le (S k) b v w.
  Proof.
    induction k as [|k' IH]; intros b v w H.
    - (* k=0 *)
      left. exact H.
    - (* k=S k' *)
      destruct H as [H | [u [Hu Hk]]].
      + left. exact H.
      + right. exists u. split; [exact Hu|].
        exact (IH b u w Hk).
  Qed.

  Lemma steps_le_mono :
    forall k k' b v w,
      k <= k' ->
      steps_le k b v w ->
      steps_le k' b v w.
  Proof.
    intros k k' b v w Hle Hsteps.
    induction Hle.
    - exact Hsteps.
    - apply steps_le_S. exact IHHle.
  Qed.

  Lemma existsb_witness {A} (f : A -> bool) (xs : list A) (x : A) :
    In x xs -> f x = true -> existsb f xs = true.
  Proof.
    intros Hin Hfx.
    apply existsb_exists.
    exists x.
    split; assumption.
  Qed.

  (** Successors in the nonprogress builder coincide with [succ_nonprogress]. *)
  Lemma succs_of_cfg_builder_nonprogress :
    forall b v,
      v < SC.cb_next b ->
      SC.succs_of (SC.cfg_builder_nonprogress b) v = succ_nonprogress b v.
  Proof.
    intros b v Hv.
    unfold SC.succs_of.
    unfold SC.lookup_succ.
    unfold SC.cfg_builder_nonprogress.
    set (n := SC.cb_next b).
    (* expose the loop definition *)
    cbn.
    (* local loop: fills all keys [0..n-1] with nonprogress_succs_of *)
    pose (loop :=
      (fix loop (k : nat) (succm : gmap nat (list nat)) : gmap nat (list nat) :=
         match k with
         | 0 => succm
         | S k' => loop k' (<[k' := SC.nonprogress_succs_of b k']> succm)
         end)).
    assert (Hlookup : loop n (∅ : gmap nat (list nat)) !! v = Some (SC.nonprogress_succs_of b v)).
    {
      subst n.
      induction (SC.cb_next b) as [|n' IHn].
      - lia.
      - simpl.
        destruct (Nat.eq_dec v n') as [->|Hneq].
        + rewrite lookup_insert. reflexivity.
        + rewrite lookup_insert_ne; [|exact Hneq].
          apply IHn.
          lia.
    }
    rewrite Hlookup.
    (* nonprogress_succs_of is exactly succ_nonprogress *)
    unfold succ_nonprogress.
    unfold SC.nonprogress_succs_of.
    destruct (SC.is_progress_vertex b v); reflexivity.
  Qed.

  Lemma edges_from_steps_le_last :
    forall b (Hclosed : builder_succ_closed b) v zs u,
      v < SC.cb_next b ->
      Forall (fun x => x < SC.cb_next b) zs ->
      FiniteDigraph.edges_from (cfg_graph_nonprogress b Hclosed) v zs ->
      FiniteDigraph.last_error zs = Some u ->
      steps_le (Nat.pred (length zs)) (SC.cfg_builder_nonprogress b) v u.
  Proof.
    intros b Hclosed v zs u Hv Hrange.
    revert v u Hv.
    induction zs as [|w zs IH]; intros v0 u0 Hv0 Hedges Hlast.
    - simpl in Hlast. discriminate.
    - destruct zs as [|w' zs'].
      + (* zs = [w] *)
        simpl in Hlast. injection Hlast as <-.
        simpl in Hedges.
        destruct Hedges as [Hw _].
        simpl.
        (* rewrite succ list to succ_nonprogress *)
        rewrite (succs_of_cfg_builder_nonprogress b v0 Hv0).
        exact Hw.
      + (* zs = w :: w' :: zs' *)
        simpl in Hedges.
        destruct Hedges as [Hvw Hrest].
        simpl in Hlast.
        (* range for the tail: w' :: zs' *)
        inversion Hrange as [|x xs Hx Hxs]; subst.
        (* w is in range, and tail range is Hxs *)
        specialize (IH w (u0) Hx Hrest Hlast).
        (* build a longer steps_le witness *)
        simpl.
        right.
        exists w.
        split.
        * rewrite (succs_of_cfg_builder_nonprogress b v0 Hv0).
          exact Hvw.
        * exact IH.
  Qed.

  (** Successor-closure for a cfg builder, using the vertex set [dom cb_label]. *)
  Definition builder_succ_closed (b : SC.cfg_builder) : Prop :=
    forall v succs,
      b.(SC.cb_succ) !! v = Some succs ->
      Forall (fun u => u ∈ dom b.(SC.cb_label)) succs.

  Definition cfg_graph (b : SC.cfg_builder) (Hclosed : builder_succ_closed b)
      : @FiniteDigraph.fin_digraph nat _ _ :=
    {| FiniteDigraph.verts := dom b.(SC.cb_label);
       FiniteDigraph.succ := SC.succs_of b;
       FiniteDigraph.succ_closed :=
         (fun v _Hv =>
            match b.(SC.cb_succ) !! v as ov return (b.(SC.cb_succ) !! v = ov -> Forall (fun u => u ∈ dom b.(SC.cb_label)) (default [] ov)) with
            | Some succs => fun H => Hclosed v succs H
            | None => fun _ => @List.Forall_nil nat (fun u => u ∈ dom b.(SC.cb_label))
            end eq_refl)
    |}.

  (** Non-progress graph: erase outgoing edges from progress vertices. *)
  Definition succ_nonprogress (b : SC.cfg_builder) (v : nat) : list nat :=
    if SC.is_progress_vertex b v then [] else SC.succs_of b v.

  Lemma succ_nonprogress_closed (b : SC.cfg_builder) (Hclosed : builder_succ_closed b) :
    forall v, v ∈ dom b.(SC.cb_label) ->
      Forall (fun u => u ∈ dom b.(SC.cb_label)) (succ_nonprogress b v).
  Proof.
    intros v _Hv.
    unfold succ_nonprogress.
    destruct (SC.is_progress_vertex b v); [constructor|].
    unfold SC.succs_of.
    destruct (b.(SC.cb_succ) !! v) as [succs|] eqn:Hsucc; [exact (Hclosed v succs Hsucc)|constructor].
  Qed.

  Definition cfg_graph_nonprogress (b : SC.cfg_builder) (Hclosed : builder_succ_closed b)
      : @FiniteDigraph.fin_digraph nat _ _ :=
    {| FiniteDigraph.verts := dom b.(SC.cb_label);
       FiniteDigraph.succ := succ_nonprogress b;
       FiniteDigraph.succ_closed := succ_nonprogress_closed b Hclosed
    |}.

  (** Progress edges: edges whose source is a progress vertex. *)
  Definition progress_edge_cfg (b : SC.cfg_builder) (v w : nat) : Prop :=
    SC.is_progress_vertex b v = true.

  (** Soundness of the boolean check (reachability-based).

      Since [SC.trace_condition_ok] is now defined via a depth-bounded
      reachability test on the non-progress graph, we can reduce soundness to
      showing that any directed cycle yields a return-to-self path of length
      bounded by [cb_next].

      The remaining combinatorial lemma (simple-cycle extraction) is stated
      separately below.
  *)

  (** Any cycle over vertices < n has a bounded return-to-self witness.

      More precisely: if [xs] is a directed cycle, then there exists some vertex
      [v] on that cycle and a path (starting at v) back to v whose length is at
      most n.

      This is a pigeonhole argument: on any walk of length > n through vertices
      drawn from a set of size n, some vertex repeats, yielding a shorter cycle.

      TODO: Fully mechanize this lemma (list slicing over edges_from).
  *)
  Lemma incl_lt_seq (n : nat) (xs : list nat) :
    Forall (fun x => x < n) xs ->
    incl xs (seq 0 n).
  Proof.
    intros Hfor x Hin.
    apply Forall_forall with (x := x) in Hfor; [|exact Hin].
    apply (proj2 (in_seq n 0 x)).
    lia.
  Qed.

  Lemma edges_from_prefix (G : FiniteDigraph.fin_digraph) (v : nat) (p s : list nat) :
    FiniteDigraph.edges_from G v (p ++ s) ->
    FiniteDigraph.edges_from G v p.
  Proof.
    revert v.
    induction p as [|w p IH]; intros v Hed; cbn.
    - exact I.
    - cbn in Hed.
      destruct Hed as [Hvw Hed'].
      split; [exact Hvw|].
      apply IH.
      (* rewrite p++s as p++s *)
      exact Hed'.
  Qed.

  Lemma edges_from_drop_until (G : FiniteDigraph.fin_digraph) (v a : nat) (l : list nat) (rest : list nat) :
    FiniteDigraph.edges_from G v (l ++ a :: rest) ->
    FiniteDigraph.edges_from G a rest.
  Proof.
    revert v.
    induction l as [|w l IH]; intros v Hed.
    - cbn in Hed. destruct Hed as [_ Hed']. exact Hed'.
    - cbn in Hed.
      destruct Hed as [_ Hed'].
      apply IH.
      exact Hed'.
  Qed.

  (** Any directed cycle over vertices < n has a bounded return-to-self witness.

      This is a pigeonhole argument: once the vertex set is bounded by n, any
      cycle contains a sub-cycle that visits at most n distinct vertices.

      We use a well-founded induction on the length of the cycle body.
  *)
  Lemma cycle_has_bounded_return :
    forall (G : FiniteDigraph.fin_digraph) (n : nat) (xs : list nat),
      (forall v, v ∈ FiniteDigraph.verts G -> v < n) ->
      FiniteDigraph.is_cycle G xs ->
      exists v ys,
        xs = v :: ys ++ [v] /\
        ys <> [] /\
        length ys <= n.
  Proof.
    intros G n xs Hbound Hcyc.
    destruct Hcyc as [v0 [ys0 [Hxs0 [Hne0 Hpath0]]]].
    remember (length ys0) as k0.
    revert v0 ys0 Hxs0 Hne0 Hpath0 Heqk0.
    induction k0 using (well_founded_induction lt_wf);
      intros v ys Hxs Hne Hpath Hk.
    destruct (le_dec (length ys) n) as [Hle|Hgt].
    - exists v, ys. repeat split; try assumption.
    - assert (Hfor : Forall (fun x => x < n) (ys ++ [v])).
      {
        destruct Hpath as [Hverts _].
        apply Forall_forall.
        intros x Hin.
        apply Hbound.
        apply Forall_forall with (x := x) in Hverts.
        + exact Hverts.
        + rewrite Hxs.
          simpl. apply in_or_app. right. exact Hin.
      }
      assert (Hincl : incl (ys ++ [v]) (seq 0 n)).
      { apply incl_lt_seq. exact Hfor. }
      destruct (NoDup_dec Nat.eq_dec (ys ++ [v])) as [Hnd|Hnnd].
      + pose proof (NoDup_incl_length _ _ Hnd Hincl) as Hlen.
        rewrite app_length in Hlen. simpl in Hlen. lia.
      + destruct (not_NoDup Nat.eq_dec Hnnd) as [a [l1 [l2 [l3 Hws]]]].
        set (ws := ys ++ [v]) in *.
        assert (Hws' : ws = l1 ++ a :: l2 ++ a :: l3) by exact Hws.
        destruct Hpath as [Hverts Hedges].
        assert (Hedges_from : FiniteDigraph.edges_from G v ws).
        { rewrite Hxs in Hedges. exact HEdges. }
        (* drop to the first [a] *)
        assert (Hafter : FiniteDigraph.edges_from G a (l2 ++ a :: l3)).
        {
          subst ws.
          rewrite Hws'.
          pose proof (edges_from_drop_until G v a l1 (l2 ++ a :: l3)) as Hdrop.
          apply Hdrop.
          rewrite <- app_assoc.
          exact Hedges_from.
        }
        (* keep only the return prefix *)
        assert (Hret : FiniteDigraph.edges_from G a (l2 ++ [a])).
        {
          replace (l2 ++ a :: l3) with ((l2 ++ [a]) ++ l3) in Hafter by (rewrite <- app_assoc; reflexivity).
          exact (edges_from_prefix G a (l2 ++ [a]) l3 Hafter).
        }
        (* build a smaller cycle list a :: l2 ++ [a] and apply IH *)
        set (xs' := a :: l2 ++ [a]).
        assert (Hpath' : FiniteDigraph.is_path G xs').
        {
          split.
          - apply Forall_forall.
            intros x Hin.
            apply Forall_forall with (x := x) in Hverts.
            + exact Hverts.
            + rewrite Hxs.
              simpl.
              apply in_or_app. right.
              subst ws. rewrite Hws'.
              (* x in xs' implies x in l1 ++ a :: l2 ++ a :: l3 *)
              unfold xs' in Hin.
              simpl in Hin.
              apply in_or_app in Hin as [Hin|Hin].
              * subst x.
                apply in_or_app. right. simpl. left. reflexivity.
              * apply in_or_app. right.
                apply in_or_app. right.
                exact Hin.
          - unfold FiniteDigraph.edges_along.
            exact Hret.
        }
        assert (Hl2 : length l2 < length ys).
        {
          subst ws.
          (* l2 is a proper sublist of ys ++ [v] *)
          assert (length l2 + 1 <= length (ys ++ [v])) by lia.
          rewrite app_length in *; simpl in *; lia.
        }
        (* Apply IH to the strictly shorter body l2. *)
        apply (H (length l2) Hl2 a l2).
        * reflexivity.
        * (* show xs' = a :: l2 ++ [a] *)
          unfold xs'. reflexivity.
        * (* body nonempty: if empty we still have self-loop cycle length 1, so handled by Hle case next *)
          intro Hnil. subst l2.
          simpl in Hgt. lia.
        * exact Hpath'.
        * reflexivity.
  Qed.




  Lemma trace_condition_ok_no_nonprogress_cycle :
    forall b (Hclosed : builder_succ_closed b) xs,
      (* Assume labels use only allocated vertices. *)
      (forall v, v ∈ dom b.(SC.cb_label) -> v < SC.cb_next b) ->
      SC.trace_condition_ok b = true ->
      FiniteDigraph.is_cycle (cfg_graph_nonprogress b Hclosed) xs ->
      False.
  Proof.
    intros b Hclosed xs Hbound Hok Hcyc.
    unfold SC.trace_condition_ok in Hok.
    apply negb_true_iff in Hok.
    unfold SC.has_nonprogress_cycle in Hok.
    set (bnp := SC.cfg_builder_nonprogress b) in *.
    set (n := SC.cb_next bnp) in *.
    destruct n as [|n']; [discriminate|].
    simpl in Hok.
    (* From the cycle in cfg_graph_nonprogress, pick its start vertex v. *)
    destruct Hcyc as [v [ys [Hxs [_Hne [Hpath]]]]].
    (* Use the boundedness assumption to ensure v < n. *)
    assert (v < S n') as Hvlt.
    {
      subst n bnp.
      (* v is in verts, hence in dom cb_label, hence < cb_next b *)
      destruct Hpath as [Hverts _].
      apply Forall_forall with (x := v) in Hverts.
      - apply Hbound.
        * apply Hverts.
          rewrite Hxs.
          simpl.
          left.
          reflexivity.
      - rewrite Hxs. simpl. left. reflexivity.
    }
    (* Use the bounded-return lemma to obtain a short return-to-self witness. *)
    pose proof (cycle_has_bounded_return (cfg_graph_nonprogress b Hclosed) (S n') xs) as Hret.
    specialize (Hret (fun v0 Hv0 => _ ) Hcyc).
    { (* bound all vertices in the nonprogress graph by cb_next *)
      intros v0 Hv0.
      (* verts are dom cb_label *)
      unfold cfg_graph_nonprogress in Hv0.
      simpl in Hv0.
      (* cb_next unchanged by cfg_builder_nonprogress *)
      subst n bnp.
      apply Hbound.
      exact Hv0.
    }
    destruct Hret as [v' [ys' [Hxs' [Hne' Hlen]]]].
    (* Reuse the path witness from [Hcyc], rewriting it using [Hxs']. *)
    destruct Hpath as [Hverts Hedges].
    (* Range facts for vertices in the cycle. *)
    assert (Hrange_xs : Forall (fun x => x < S n') xs).
    {
      (* all vertices are in dom cb_label by Hverts, hence < cb_next b = S n' *)
      apply Forall_forall.
      intros x Hinx.
      apply Forall_forall with (x := x) in Hverts; [|exact Hinx].
      subst n bnp.
      apply Hbound.
      exact Hverts.
    }
    (* Use the bounded-return decomposition for a short cycle shape. *)
    rewrite Hxs' in Hrange_xs.
    inversion Hrange_xs as [|x0 xs0 Hx0 Htail]; subst x0 xs0.
    assert (Hrange_tail : Forall (fun x => x < S n') (ys' ++ [v'])).
    { exact Htail. }

    (* Extract edges_from along the tail from edges_along. *)
    assert (Hedges_from : FiniteDigraph.edges_from (cfg_graph_nonprogress b Hclosed) v' (ys' ++ [v'])).
    {
      rewrite Hxs' in Hedges.
      exact Hedges.
    }

    (* last_error (ys' ++ [v']) = Some v' *)
    assert (Hlast : FiniteDigraph.last_error (ys' ++ [v']) = Some v').
    {
      induction ys' as [|a ys'' IH]; cbn.
      - reflexivity.
      - destruct ys''; cbn; exact IH.
    }

    (* Convert edges_from to a bounded steps_le witness. *)
    assert (Hsteps0 : steps_le (Nat.pred (length (ys' ++ [v']))) (SC.cfg_builder_nonprogress b) v' v').
    {
      apply (edges_from_steps_le_last b Hclosed v' (ys' ++ [v']) v').
      - exact Hvlt.
      - exact Hrange_tail.
      - exact Hedges_from.
      - exact Hlast.
    }

    (* simplify pred length (ys' ++ [v']) = length ys' *)
    assert (Hpred : Nat.pred (length (ys' ++ [v'])) = length ys').
    { rewrite app_length. simpl. lia. }
    rewrite Hpred in Hsteps0.

    (* Lift steps_le to the checker depth [S n'] using Hlen. *)
    assert (Hsteps : steps_le (S n') (SC.cfg_builder_nonprogress b) v' v').
    {
      eapply steps_le_mono.
      - exact Hlen.
      - exact Hsteps0.
    }

    (* Now the checker’s reach_depth witnesses v' ∈ reach_depth (S n') v'. *)
    assert (Hin : In v' (SC.reach_depth (S n') (SC.cfg_builder_nonprogress b) v')).
    { apply steps_le_in_reach_depth. exact Hsteps. }
    assert (Hmem : SC.mem_nat v' (SC.reach_depth (S n') (SC.cfg_builder_nonprogress b) v') = true).
    { apply mem_nat_true_iff. exact Hin. }

    (* Show existsb detects the cycle at v'. *)
    assert (Hinseq : In v' (seq 0 (S n'))).
    { apply (proj2 (in_seq (S n') 0 v')). lia. }
    assert (Hcycle : SC.has_cycle_by_depth (S n') (SC.cfg_builder_nonprogress b) (S n') = true).
    {
      unfold SC.has_cycle_by_depth.
      eapply existsb_witness; [exact Hinseq|].
      exact Hmem.
    }

    (* Contradiction with [trace_condition_ok] being true. *)
    subst n bnp.
    (* Hok : has_nonprogress_cycle b = false *)
    rewrite Hcycle in Hok.
    discriminate.
  Qed.

  (** If a cycle has no progress edge, it is also a cycle in the non-progress graph. *)
  Lemma cycle_no_progress_implies_cycle_nonprogress :
    forall b (Hclosed : builder_succ_closed b) xs,
      FiniteDigraph.is_cycle (cfg_graph b Hclosed) xs ->
      ~ Ranking.has_progress_edge (V := nat) (progress_edge_cfg b) xs ->
      FiniteDigraph.is_cycle (cfg_graph_nonprogress b Hclosed) xs.
  Proof.
    intros b Hclosed xs Hcyc Hnprog.
    destruct Hcyc as [v [ys [-> [Hne [Hpath]]]]].
    exists v, ys.
    split; [reflexivity|].
    split; [exact Hne|].
    destruct Hpath as [Hverts Hedges].
    split; [exact Hverts|].
    (* show all edges remain, since no source vertex is progress *)
    revert v Hedges Hnprog.
    induction ys as [|w ys IH]; intros v0 Hedges0 Hnprog0.
    - cbn in Hedges0. exact I.
    - cbn in Hedges0.
      destruct Hedges0 as [Hvw Hrest].
      split.
      + (* edge v0 -> w in nonprogress graph *)
        unfold succ_nonprogress.
        (* no progress edge at the head *)
        assert (SC.is_progress_vertex b v0 = false) as Hv0np.
        {
          destruct (SC.is_progress_vertex b v0) eqn:Hpv; [|reflexivity].
          exfalso.
          apply Hnprog0.
          (* has_progress_edge (v0 :: w :: ys) holds by the head edge *)
          cbn.
          left.
          unfold progress_edge_cfg.
          exact Hpv.
        }
        rewrite Hv0np.
        exact Hvw.
      + (* tail *)
        apply (IH w Hrest).
        (* strengthen "no progress" to tail *)
        intro Htail.
        apply Hnprog0.
        cbn.
        right.
        exact Htail.
  Qed.

  (** Main theorem: if the trace check succeeds, then every cycle contains a progress edge. *)
  Theorem trace_condition_ok_cycle_progress :
    forall b (Hclosed : builder_succ_closed b) xs,
      SC.trace_condition_ok b = true ->
      FiniteDigraph.is_cycle (cfg_graph b Hclosed) xs ->
      Ranking.has_progress_edge (V := nat) (progress_edge_cfg b) xs.
  Proof.
    intros b Hclosed xs Hok Hcyc.
    destruct (classic (Ranking.has_progress_edge (V := nat) (progress_edge_cfg b) xs)) as [Hp|Hnp]; [exact Hp|].
    exfalso.
    pose proof (cycle_no_progress_implies_cycle_nonprogress b Hclosed xs Hcyc Hnp) as Hcyc_np.
    exact (trace_condition_ok_no_nonprogress_cycle b Hclosed xs Hok Hcyc_np).
  Qed.

End CycleProgress.

(** Helpers for the CIU proof: label lookup for successors, and
    self-loop detection via trace check. *)

Lemma builder_succ_closed_label (b : SC.cfg_builder) (Hclosed : builder_succ_closed b)
    (v w : nat) (cfg0 : SC.config) (succs : list nat) :
  b.(SC.cb_label) !! v = Some cfg0 ->
  b.(SC.cb_succ) !! v = Some succs ->
  In w succs ->
  exists cfg, b.(SC.cb_label) !! w = Some cfg.
Proof.
  intros Hlabel Hsucc Hin.
  unfold builder_succ_closed in Hclosed.
  pose proof (Hclosed v succs Hsucc) as Hfor.
  apply Forall_forall with (x := w) in Hfor; [|exact Hin].
  apply elem_of_dom in Hfor. exact Hfor.
Qed.

Lemma trace_condition_ok_no_self_loop (b : SC.cfg_builder)
    (Hclosed : builder_succ_closed b) (v : nat) (cfg : SC.config) :
  SC.trace_condition_ok b = true ->
  b.(SC.cb_succ) !! v = Some [v] ->
  b.(SC.cb_label) !! v = Some cfg ->
  False.
Proof.
  intros Hok Hsucc Hlabel.
  (* Self-loop [v;v;v] is a cycle with no progress edge *)
  apply (trace_condition_ok_cycle_progress b Hclosed [v; v; v] Hok).
  exists v, [v]. split; [reflexivity|split; [discriminate|]].
  split.
  - apply Forall_forall. intros x Hin.
    repeat (match goal with H: In x [v;v;v] |- _ => destruct H as [->|[->|[->|[]]]] end).
    all: apply elem_of_dom; exists cfg; exact Hlabel.
  - cbn. split.
    + unfold cfg_graph. cbn.
      apply elem_of_list_filter. split.
      * exact (in_eq v nil).
      * apply bool_decide_true. apply elem_of_dom_2. exact Hlabel.
    + exact I.
Qed.
