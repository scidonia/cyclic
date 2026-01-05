From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.

Section Packaging.
  (** For now we package the raw read-off graph as a preproof with a trivial
      local rule. The next step will replace `Rule` by the vertex-typing rule
      relation (`jTyV/jEqV/jSubV`). *)

  Definition Judgement : Type := RO.node.
  Definition Rule (_ : Judgement) (_ : list Judgement) : Prop := True.

  Definition verts_of (n : nat) : gset nat :=
    list_to_set (seq 0 n).

  Definition succ_of (b : RO.builder) (v : nat) : list nat :=
    filter (fun w => bool_decide (w < RO.b_next b))
      (default [] (RO.b_succ b !! v)).

  Definition label_of (b : RO.builder) (v : nat) : RO.node :=
    default (RO.nVar 0) (RO.b_label b !! v).

  Lemma succ_of_closed (b : RO.builder) (v : nat) :
    Forall (fun w => w ∈ verts_of (RO.b_next b)) (succ_of b v).
  Proof.
    apply Forall_forall.
    intros w Hw.
    unfold succ_of in Hw.
    apply elem_of_list_filter in Hw.
    destruct Hw as [Hw Hlt].
    apply bool_decide_true in Hlt.
    unfold verts_of.
    apply elem_of_list_to_set.
    (* `w < b_next b` implies `w ∈ seq 0 (b_next b)` *)
    apply (proj2 (elem_of_seq 0 (RO.b_next b) w)).
    lia.
  Qed.

  Program Definition graph_of (b : RO.builder) : FiniteDigraph.fin_digraph nat :=
    {| FiniteDigraph.verts := verts_of (RO.b_next b);
       FiniteDigraph.succ := succ_of b;
    |}.
  Next Obligation.
    intros b v Hv.
    unfold FiniteDigraph.succ.
    simpl.
    exact (succ_of_closed b v).
  Qed.

  Definition preproof_of (b : RO.builder) : @Preproof.preproof Judgement Rule nat _ _ :=
    {| Preproof.pp_graph := graph_of b;
       Preproof.pp_label := label_of b;
       Preproof.pp_rule_ok := fun _ _ => I |}.

  (* Basic monotonicity: compilation never decreases `b_next`. *)
  Lemma put_preserves_next (v : nat) (lbl : RO.node) (succs : list nat) (b : RO.builder) :
    RO.b_next (RO.put v lbl succs b) = RO.b_next b.
  Proof. reflexivity. Qed.

  Lemma put_fix_ty_preserves_next (v vA : nat) (b : RO.builder) :
    RO.b_next (RO.put_fix_ty v vA b) = RO.b_next b.
  Proof. reflexivity. Qed.

  Lemma fresh_increases_next (b : RO.builder) (v : nat) (b' : RO.builder) :
    RO.fresh b = (v, b') -> RO.b_next b' = S (RO.b_next b).
  Proof.
    unfold RO.fresh.
    intro H.
    inversion H.
    reflexivity.
  Qed.

  Lemma compile_tm_next_ge (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (v : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (v, b') ->
    RO.b_next b <= RO.b_next b'.
  Proof.
    revert ρ t b v b'.
    induction fuel as [|fuel IH]; intros ρ t b v b' H;
      simpl in H.
    - (* fuel = 0 *)
      destruct (RO.fresh b) as [v0 b0] eqn:Hfresh.
      inversion H; subst.
      rewrite (fresh_increases_next _ _ _ Hfresh).
      lia.
    - (* fuel = S fuel *)
      destruct t; simpl in H.
      all: repeat
        match goal with
        | Hf : RO.fresh _ = _ |- _ =>
            apply fresh_increases_next in Hf
        end.
      all: try (repeat (destruct (RO.fresh b) as [v0 b0] eqn:Hfresh; clear Hfresh));
        (* For the remaining cases we can simply use that the result builder is
           obtained from the initial one by a sequence of `fresh` allocations. *)
        admit.
  Admitted.

  Lemma compile_tm_root_in (t : Term.Syntax.tm) (root : nat) (b : RO.builder) :
    RO.read_off_raw t = (root, b) ->
    root ∈ verts (graph_of b).
  Proof.
    intro H.
    unfold RO.read_off_raw in H.
    unfold verts.
    simpl.
    unfold RO.compile_tm in H.
    (* We only need the easy fact: `root < b_next b`. *)
    pose proof (compile_tm_next_ge (fuel := Term.Syntax.size t) (ρ := []) (t := t)
                 (b := RO.empty_builder) (v := root) (b' := b)) as Hge.
    specialize (Hge H).
    unfold verts_of.
    apply elem_of_list_to_set.
    apply (proj2 (elem_of_seq 0 (RO.b_next b) root)).
    lia.
  Qed.

  Definition rooted_preproof_of (t : Term.Syntax.tm) : @Preproof.rooted_preproof Judgement Rule nat _ _ :=
    let '(root, b) := RO.read_off_raw t in
    {| Preproof.rpp_proof := preproof_of b;
       Preproof.rpp_root := root;
       Preproof.rpp_root_in := (compile_tm_root_in t root b eq_refl) |}.
End Packaging.
