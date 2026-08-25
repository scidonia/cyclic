From Stdlib Require Import List ListDec Bool Arith Lia Utf8 Classical.
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
        * left. symmetry. exact H.
        * right. exact H.
  Qed.

  Lemma mem_nat_false_iff (x : nat) (xs : list nat) :
    SC.mem_nat x xs = false <-> ~ In x xs.
  Proof.
    rewrite <- mem_nat_true_iff.
    destruct (SC.mem_nat x xs); split; congruence.
  Qed.

    Lemma existsb_Nat_eqb_eq (a : nat) (l : list nat) :
    existsb (Nat.eqb a) l = true -> In a l.
  Proof.
    induction l as [|x l IH]; cbn; [discriminate|].
    destruct (Nat.eqb a x) eqn:Heq.
    - intros _. apply Nat.eqb_eq in Heq. subst. apply in_eq.
    - intro H. apply IH in H. apply in_cons, H.
  Qed.

Lemma in_nub_nat_iff (x : nat) (xs : list nat) :
    In x (SC.nub_nat xs) <-> In x xs.
  Proof.
    induction xs as [|y ys IH]; cbn.
    - tauto.
    - destruct (existsb (Nat.eqb y) (SC.nub_nat ys)) eqn:Hex.
      + apply existsb_Nat_eqb_eq in Hex.
        rewrite IH. split.
        * intros Hx. right. exact Hx.
        * intros [<-|Hx]; try exact Hx.
          apply IH. exact Hex.
      + split.
        * intros [<-|Hx]; [left; reflexivity|right; apply IH; exact Hx].
        * intros [<-|Hx]; [left; reflexivity|right; apply IH; exact Hx].
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

  Definition succ_nonprogress (b : SC.cfg_builder) (v : nat) : list nat :=
    if SC.is_progress_vertex b v then [] else SC.succs_of b v.

  (** Descending fill loop, as used by [cfg_builder_nonprogress], does not
      touch keys at or above the loop bound. *)
  Lemma fill_loop_untouched {A : Type} (f : nat -> A) :
    forall n m k, n <= k ->
      (fix loop (j : nat) (acc : gmap nat A) : gmap nat A :=
         match j with 0 => acc | S j' => loop j' (<[j' := f j']> acc) end)
        n m !! k = m !! k.
  Proof.
    intros n m k Hle.
    induction n as [|n' IHn] in m, k, Hle |- *.
    - cbn. reflexivity.
    - cbn.
      rewrite (IHn (<[n' := f n']> m) k) by lia.
      rewrite lookup_insert_ne by lia.
      reflexivity.
  Qed.

  (** A descending fill loop maps every key below the bound to [f]. *)
  Lemma fill_loop_lookup {A : Type} (f : nat -> A) :
    forall n m v, v < n ->
      (fix loop (j : nat) (acc : gmap nat A) : gmap nat A :=
         match j with 0 => acc | S j' => loop j' (<[j' := f j']> acc) end)
        n m !! v = Some (f v).
  Proof.
    intros n m v Hv.
    induction n as [|n' IHn] in m, v, Hv |- *.
    - lia.
    - cbn.
      destruct (Nat.eq_dec v n') as [->|Hneq].
      + rewrite (fill_loop_untouched f n' _ n') by lia.
        rewrite lookup_insert. reflexivity.
      + apply (IHn (<[n' := f n']> m) v). lia.
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
    cbn.
    rewrite (fill_loop_lookup (SC.nonprogress_succs_of b) (SC.cb_next b) (∅ : gmap nat (list nat)) v Hv).
    (* nonprogress_succs_of is exactly succ_nonprogress *)
    unfold succ_nonprogress.
    unfold SC.nonprogress_succs_of.
    destruct (SC.is_progress_vertex b v); reflexivity.
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

  Lemma succ_nonprogress_closed (b : SC.cfg_builder) (Hclosed : builder_succ_closed b) :
    forall v, v ∈ dom b.(SC.cb_label) ->
      Forall (fun u => u ∈ dom b.(SC.cb_label)) (succ_nonprogress b v).
  Proof.
    intros v _Hv.
    unfold succ_nonprogress.
    destruct (SC.is_progress_vertex b v); [constructor|].
    unfold SC.succs_of, SC.lookup_succ.
    destruct (b.(SC.cb_succ) !! v) as [succs|] eqn:Hsucc.
    - cbn. exact (Hclosed v succs Hsucc).
    - constructor.
  Qed.

  Definition cfg_graph_nonprogress (b : SC.cfg_builder) (Hclosed : builder_succ_closed b)
      : @FiniteDigraph.fin_digraph nat _ _ :=
    {| FiniteDigraph.verts := dom b.(SC.cb_label);
       FiniteDigraph.succ := succ_nonprogress b;
       FiniteDigraph.succ_closed := succ_nonprogress_closed b Hclosed
    |}.

  Lemma edges_from_steps_le_last :
    forall b (Hclosed : builder_succ_closed b) v zs u,
      v < SC.cb_next b ->
      Forall (fun x => x < SC.cb_next b) zs ->
      @FiniteDigraph.edges_from nat _ _ (cfg_graph_nonprogress b Hclosed) v zs ->
      FiniteDigraph.last_error nat zs = Some u ->
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
        rewrite elem_of_list_In in Hw. exact Hw.
      + (* zs = w :: w' :: zs' *)
        simpl in Hedges.
        destruct Hedges as [Hvw Hrest].
        simpl in Hlast.
        (* range for the tail: w' :: zs' *)
        inversion Hrange as [|x xs Hx Hxs]; subst.
        (* w is in range, and tail range is Hxs *)
        specialize (IH Hxs w u0 Hx Hrest Hlast).
        (* build a longer steps_le witness *)
        simpl.
        right.
        exists w.
        split.
        * rewrite (succs_of_cfg_builder_nonprogress b v0 Hv0).
          rewrite elem_of_list_In in Hvw. exact Hvw.
        * exact IH.
  Qed.

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
    apply List.Forall_forall with (x := x) in Hfor; [|exact Hin].
    apply (proj2 (in_seq n 0 x)).
    lia.
  Qed.

  Lemma edges_from_prefix (G : @FiniteDigraph.fin_digraph nat _ _) (v : nat) (p s : list nat) :
    @FiniteDigraph.edges_from nat _ _ G v (p ++ s) ->
    @FiniteDigraph.edges_from nat _ _ G v p.
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

  Lemma edges_from_drop_until (G : @FiniteDigraph.fin_digraph nat _ _) (v a : nat) (l : list nat) (rest : list nat) :
    @FiniteDigraph.edges_from nat _ _ G v (l ++ a :: rest) ->
    @FiniteDigraph.edges_from nat _ _ G a rest.
  Proof.
    revert v.
    induction l as [|w l IH]; intros v Hed.
    - cbn in Hed. destruct Hed as [_ Hed']. exact Hed'.
    - cbn in Hed.
      destruct Hed as [_ Hed'].
      exact (IH w Hed').
  Qed.

  (** Any directed cycle over vertices < n has a bounded return-to-self witness.

      This is a pigeonhole argument: once the vertex set is bounded by n, any
      cycle contains a sub-cycle that visits at most n distinct vertices.

      We use a well-founded induction on the length of the cycle body.
  *)
  Lemma not_NoDup_repeat (l : list nat) :
    ~ List.NoDup l -> exists x (l1 l2 l3 : list nat), l = l1 ++ x :: l2 ++ x :: l3.
  Proof.
    induction l as [|a l' IH]; intros Hnd.
    - exfalso. apply Hnd. constructor.
    - cbn in Hnd.
      destruct (In_dec Nat.eq_dec a l') as [Hin|Hnin].
      + apply in_split in Hin as [l1 [l2 Hl']].
        exists a, [], l1, l2. cbn. rewrite Hl'. reflexivity.
      + assert (Hnd' : ~ List.NoDup l'). { intro Hl'. apply Hnd. constructor; [exact Hnin|exact Hl']. }
        apply IH in Hnd'.
        destruct Hnd' as [x [l1 [l2 [l3 Hl']]]].
        exists x, (a :: l1), l2, l3. cbn. rewrite Hl'. reflexivity.
  Qed.

  Lemma In_cons_prefix (x a : nat) (l2 l3 : list nat) :
    In x (a :: l2 ++ [a]) -> In x (a :: l2 ++ a :: l3).
  Proof.
    intros Hin.
    simpl in Hin. destruct Hin as [Hxa|Hinl2].
    - simpl. left. exact Hxa.
    - apply in_app_or in Hinl2 as [Hl2|Hsingle].
      + simpl. right. apply in_or_app. left. exact Hl2.
    + simpl in Hsingle. simpl. right. apply in_or_app. right. simpl.
      destruct Hsingle as [Hax|[]]; left; exact Hax.
Qed.

  Lemma cycle_has_bounded_return :
    forall (G : @FiniteDigraph.fin_digraph nat _ _) (n : nat) (xs : list nat),
      (forall v, v ∈ FiniteDigraph.verts G -> v < n) ->
      @FiniteDigraph.is_cycle nat _ _ G xs ->
      exists v ys,
        @FiniteDigraph.is_path nat _ _ G (v :: ys ++ [v]) /\
        ys <> [] /\
        length ys <= n.
  Proof.
    intros G n xs Hbound Hcyc.
    destruct Hcyc as [v0 [ys0 [Hxs0 [Hne0 Hpath0]]]].
    assert (Hmain : forall xs0, @FiniteDigraph.is_path nat _ _ G xs0 ->
        (exists v ys, xs0 = v :: ys ++ [v] /\ ys <> []) ->
        exists v ys, @FiniteDigraph.is_path nat _ _ G (v :: ys ++ [v]) /\ ys <> [] /\ length ys <= n).
    {
      refine (well_founded_ind (well_founded_ltof (list nat) (fun xs0 => length xs0)) _ _).
      intros xs0 IH Hpath [v [ys [Hxs Hne]]].
      destruct (le_dec (length ys) n) as [Hle|Hgt].
      - exists v, ys. split; [|split]; [|exact Hne|exact Hle].
        rewrite <- Hxs. exact Hpath.
      - destruct Hpath as [Hverts Hedges].
        assert (Hfor : Forall (fun x => x < n) (ys ++ [v])).
        {
          apply List.Forall_forall.
          intros x Hin.
          apply Hbound.
          apply List.Forall_forall with (x := x) in Hverts; [exact Hverts|].
          rewrite Hxs. simpl. right. exact Hin.
        }
        assert (Hincl : incl (ys ++ [v]) (seq 0 n)).
        { apply incl_lt_seq. exact Hfor. }
        destruct (NoDup_dec (ys ++ [v])) as [Hnd|Hnnd].
        + apply NoDup_ListNoDup in Hnd.
          pose proof (@NoDup_incl_length nat (ys ++ [v]) (seq 0 n) Hnd Hincl) as Hlen.
          rewrite app_length in Hlen. rewrite seq_length in Hlen. simpl in Hlen. lia.
        + rewrite NoDup_ListNoDup in Hnnd.
          apply not_NoDup_repeat in Hnnd as [a [l1 [l2 [l3 Hws]]]].
          assert (Hedges_from : @FiniteDigraph.edges_from nat _ _ G v (ys ++ [v])).
          { rewrite Hxs in Hedges. cbn in Hedges. exact Hedges. }
          assert (Hafter : @FiniteDigraph.edges_from nat _ _ G a (l2 ++ a :: l3)).
          {
            apply (edges_from_drop_until G v a l1 (l2 ++ a :: l3)).
            rewrite <- Hws. exact Hedges_from.
          }
          assert (Hret : @FiniteDigraph.edges_from nat _ _ G a (l2 ++ [a])).
          {
            apply (edges_from_prefix G a (l2 ++ [a]) l3).
            rewrite <- app_assoc. exact Hafter.
          }
          assert (Ha_verts : a ∈ FiniteDigraph.verts G).
          {
            apply List.Forall_forall with (x := a) in Hverts; [exact Hverts|].
            rewrite Hxs. simpl. right. rewrite Hws.
            apply in_or_app. right. simpl. left. reflexivity.
          }
          destruct l2 as [|b l2'].
          * (* self-loop: a -> a *)
            assert (Hloop : a ∈ FiniteDigraph.succ G a).
            { cbn in Hret. destruct Hret as [Hloop _]. exact Hloop. }
            assert (Ha_n : a < n) by (apply Hbound; exact Ha_verts).
            exists a, [a].
            { split.
              { split.
                - apply List.Forall_forall.
                  intros x Hinx.
                  cbn in Hinx. destruct Hinx as [->|Hinx1]; [exact Ha_verts|].
                  cbn in Hinx1. destruct Hinx1 as [->|Hinx2]; [exact Ha_verts|].
                  cbn in Hinx2. destruct Hinx2 as [->|Hinx3]; [exact Ha_verts|contradiction].
                - change (a ∈ FiniteDigraph.succ G a ∧ (a ∈ FiniteDigraph.succ G a ∧ True)).
                  exact (conj Hloop (conj Hloop I)). }
              split.
              - discriminate.
              - simpl. lia. }
          * (* l2 = b :: l2' nonempty *)
            assert (Hpath' : @FiniteDigraph.is_path nat _ _ G (a :: b :: l2' ++ [a])).
            {
              split.
              - apply List.Forall_forall.
                intros x Hinx.
                apply List.Forall_forall with (x := x) in Hverts; [exact Hverts|].
                rewrite Hxs. simpl. right. rewrite Hws.
                apply in_or_app. right. exact (In_cons_prefix x a (b :: l2') l3 Hinx).
              - cbn. exact Hret.
            }
            assert (Hl2 : length (a :: b :: l2' ++ [a]) < length xs0).
            { rewrite Hxs, Hws.
              repeat (try rewrite !app_length; try simpl).
              lia. }
            apply (IH (a :: b :: l2' ++ [a]) Hl2 Hpath').
            exists a, (b :: l2'). split; [reflexivity|].
            intro Hnil. discriminate.
    }
    apply (Hmain xs Hpath0).
    exists v0, ys0. split; [exact Hxs0|exact Hne0].
  Qed.




  Lemma last_error_snoc (ys : list nat) (v : nat) :
    FiniteDigraph.last_error nat (ys ++ [v]) = Some v.
  Proof.
    induction ys as [|a ys'' IH]; cbn.
    - reflexivity.
    - destruct ys''; cbn; [reflexivity|exact IH].
  Qed.

  Lemma trace_condition_ok_no_nonprogress_cycle :
    forall b (Hclosed : builder_succ_closed b) xs,
      (* Assume labels use only allocated vertices. *)
      (forall v, v ∈ dom b.(SC.cb_label) -> v < SC.cb_next b) ->
      SC.trace_condition_ok b = true ->
      @FiniteDigraph.is_cycle nat _ _ (cfg_graph_nonprogress b Hclosed) xs ->
      False.
  Proof.
    intros b Hclosed xs Hbound Hok Hcyc.
    unfold SC.trace_condition_ok in Hok.
    apply negb_true_iff in Hok.
    unfold SC.has_nonprogress_cycle in Hok.
    cbv zeta in Hok.
    change (SC.cb_next (SC.cfg_builder_nonprogress b)) with (SC.cb_next b) in Hok.
    remember (SC.cb_next b) as cb eqn:Hcb in Hok.
    destruct cb as [|n'].
    - (* cb_next b = 0 : no allocated vertices, so no cycle *)
      destruct Hcyc as [v [ys [Hxs [_ Hpath]]]].
      destruct Hpath as [Hverts _].
      apply List.Forall_forall with (x := v) in Hverts; [|rewrite Hxs; simpl; left; reflexivity].
      unfold cfg_graph_nonprogress in Hverts. cbn in Hverts.
      apply Hbound in Hverts. lia.
    - (* cb_next b = S n' *)
      cbv iota in Hok.
      assert (Hbound' : forall v0, v0 ∈ FiniteDigraph.verts (cfg_graph_nonprogress b Hclosed) -> v0 < S n').
      {
        intros v0 Hv0. unfold cfg_graph_nonprogress in Hv0. cbn in Hv0.
        apply Hbound in Hv0. rewrite <- Hcb in Hv0. exact Hv0.
      }
      pose proof (cycle_has_bounded_return (cfg_graph_nonprogress b Hclosed) (S n') xs Hbound' Hcyc)
        as [v' [ys' [Hpath' [Hne' Hlen]]]].
      destruct Hpath' as [Hverts' Hedges'].
      assert (Hvlt : v' < S n').
      {
        apply List.Forall_forall with (x := v') in Hverts'; [|simpl; left; reflexivity].
        unfold cfg_graph_nonprogress in Hverts'. cbn in Hverts'.
        apply Hbound in Hverts'. rewrite <- Hcb in Hverts'. exact Hverts'.
      }
      assert (Hrange_tail : Forall (fun x => x < S n') (ys' ++ [v'])).
      {
        apply List.Forall_forall.
        intros x Hinx.
        apply List.Forall_forall with (x := x) in Hverts'; [|simpl; right; exact Hinx].
        unfold cfg_graph_nonprogress in Hverts'. cbn in Hverts'.
        apply Hbound in Hverts'. rewrite <- Hcb in Hverts'. exact Hverts'.
      }
      assert (Hedges_from : @FiniteDigraph.edges_from nat _ _ (cfg_graph_nonprogress b Hclosed) v' (ys' ++ [v'])).
      { cbn in Hedges'. exact Hedges'. }
      assert (Hlast : FiniteDigraph.last_error nat (ys' ++ [v']) = Some v').
      { apply last_error_snoc. }
      assert (Hsteps0 : steps_le (Nat.pred (length (ys' ++ [v']))) (SC.cfg_builder_nonprogress b) v' v').
      {
        apply (edges_from_steps_le_last b Hclosed v' (ys' ++ [v']) v').
        - rewrite <- Hcb. exact Hvlt.
        - rewrite <- Hcb. exact Hrange_tail.
        - exact Hedges_from.
        - exact Hlast.
      }
      assert (Hpred : Nat.pred (length (ys' ++ [v'])) = length ys').
      { rewrite app_length. simpl. lia. }
      rewrite Hpred in Hsteps0.
      assert (Hsteps : steps_le (S n') (SC.cfg_builder_nonprogress b) v' v').
      { eapply steps_le_mono. - exact Hlen. - exact Hsteps0. }
      assert (Hin : In v' (SC.reach_depth (S n') (SC.cfg_builder_nonprogress b) v')).
      { apply steps_le_in_reach_depth. exact Hsteps. }
      assert (Hmem : SC.mem_nat v' (SC.reach_depth (S n') (SC.cfg_builder_nonprogress b) v') = true).
      { apply mem_nat_true_iff. exact Hin. }
      assert (Hinseq : In v' (seq 0 (S n'))).
      { apply (proj2 (in_seq (S n') 0 v')). lia. }
      assert (Hcycle : SC.has_cycle_by_depth (S n') (SC.cfg_builder_nonprogress b) (S n') = true).
      {
        unfold SC.has_cycle_by_depth.
        eapply existsb_witness; [exact Hinseq|].
        exact Hmem.
      }
      change (SC.has_cycle_by_depth (S n') (SC.cfg_builder_nonprogress b) (S n') = false) in Hok.
      rewrite Hcycle in Hok. discriminate.
  Qed.

  (** If a cycle has no progress edge, it is also a cycle in the non-progress graph. *)

  Lemma edges_along_nonprogress_preserved :
    forall b (Hclosed : builder_succ_closed b) (xs : list nat),
      FiniteDigraph.edges_along nat (cfg_graph b Hclosed) xs ->
      ~ Ranking.has_progress_edge nat (progress_edge_cfg b) xs ->
      FiniteDigraph.edges_along nat (cfg_graph_nonprogress b Hclosed) xs.
  Proof.
    intros b Hclosed xs.
    induction xs as [|v xs IH]; intros Hedges Hnprog.
    - exact I.
    - destruct xs as [|w rest].
      + exact I.
      + cbn in Hedges. destruct Hedges as [Hvw Hrest].
        cbn. split.
        * change (w ∈ succ_nonprogress b v).
          assert (Hvnp : SC.is_progress_vertex b v = false).
          { destruct (SC.is_progress_vertex b v) eqn:Hpv; [|reflexivity].
            exfalso. apply Hnprog. cbn. left. unfold progress_edge_cfg. exact Hpv. }
          unfold succ_nonprogress. rewrite Hvnp. exact Hvw.
        * apply IH.
          -- exact Hrest.
          -- intro Htail. apply Hnprog. cbn. right. exact Htail.
  Qed.

  Lemma cycle_no_progress_implies_cycle_nonprogress :
    forall b (Hclosed : builder_succ_closed b) xs,
      @FiniteDigraph.is_cycle nat _ _ (cfg_graph b Hclosed) xs ->
      ~ Ranking.has_progress_edge nat (progress_edge_cfg b) xs ->
      @FiniteDigraph.is_cycle nat _ _ (cfg_graph_nonprogress b Hclosed) xs.
  Proof.
    intros b Hclosed xs Hcyc Hnprog.
    destruct Hcyc as [v [ys [Hxs [Hne Hpath]]]].
    subst xs.
    exists v, ys. split; [reflexivity|split; [exact Hne|]].
    destruct Hpath as [Hverts Hedges].
    split; [exact Hverts|].
    apply edges_along_nonprogress_preserved.
    - exact Hedges.
    - exact Hnprog.
  Qed.

  (** Main theorem: if the trace check succeeds, then every cycle contains a progress edge. *)
  Theorem trace_condition_ok_cycle_progress :
    forall b (Hclosed : builder_succ_closed b) xs,
      (forall v, v ∈ dom b.(SC.cb_label) -> v < SC.cb_next b) ->
      SC.trace_condition_ok b = true ->
      @FiniteDigraph.is_cycle nat _ _ (cfg_graph b Hclosed) xs ->
      Ranking.has_progress_edge nat (progress_edge_cfg b) xs.
  Proof.
    intros b Hclosed xs Hbound Hok Hcyc.
    destruct (classic (Ranking.has_progress_edge nat (progress_edge_cfg b) xs)) as [Hp|Hnp]; [exact Hp|].
    exfalso.
    pose proof (cycle_no_progress_implies_cycle_nonprogress b Hclosed xs Hcyc Hnp) as Hcyc_np.
    exact (trace_condition_ok_no_nonprogress_cycle b Hclosed xs Hbound Hok Hcyc_np).
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
  apply List.Forall_forall with (x := w) in Hfor; [|exact Hin].
  apply elem_of_dom in Hfor. exact Hfor.
Qed.

Lemma trace_condition_ok_no_self_loop (b : SC.cfg_builder)
    (Hclosed : builder_succ_closed b) (v : nat) (cfg : SC.config) :
  (forall w, w ∈ dom b.(SC.cb_label) -> w < SC.cb_next b) ->
  SC.is_progress_vertex b v = false ->
  SC.trace_condition_ok b = true ->
  b.(SC.cb_succ) !! v = Some [v] ->
  b.(SC.cb_label) !! v = Some cfg ->
  False.
Proof.
  intros Hbound Hvnp Hok Hsucc Hlabel.
  eapply (trace_condition_ok_no_nonprogress_cycle b Hclosed [v; v; v] Hbound Hok).
  exists v, [v]. split; [reflexivity|split; [discriminate|]].
  split.
  - apply List.Forall_forall. intros x Hin.
    cbn in Hin. repeat (destruct Hin as [Hvx|Hin]; [subst x|cbn in Hin]).
    all: try contradiction.
    all: apply (elem_of_dom_2 b.(SC.cb_label) v cfg Hlabel).
  - cbn. split.
    + unfold cfg_graph_nonprogress, succ_nonprogress. cbn. rewrite Hvnp.
      unfold SC.succs_of, SC.lookup_succ. cbn. rewrite Hsucc. cbn.
      rewrite elem_of_list_In. cbn. left. reflexivity.
    + split.
      * unfold cfg_graph_nonprogress, succ_nonprogress. cbn. rewrite Hvnp.
        unfold SC.succs_of, SC.lookup_succ. cbn. rewrite Hsucc. cbn.
        rewrite elem_of_list_In. cbn. left. reflexivity.
      * exact I.
Qed.
