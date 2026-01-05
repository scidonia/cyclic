From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.

Section Packaging.
  (** Package the raw read-off graph as a rooted preproof.

      For now, the local rule is trivial (`True`). This step exists to move from
      “maps representing a cyclic graph” to the project’s standard `preproof`
      structure.

      Next step: replace `Rule` by the vertex-typing/equality/substitution rule
      relation (`jTyV/jEqV/jSubV`) and prove `pp_rule_ok` by construction.
  *)

  Definition Judgement : Type := RO.node.
  Definition Rule (_ : Judgement) (_ : list Judgement) : Prop := True.

  Definition verts_of (b : RO.builder) : gset nat :=
    dom (RO.b_label b).

  Definition succ_of (b : RO.builder) (v : nat) : list nat :=
    filter (fun w => bool_decide (w ∈ verts_of b))
      (default [] (RO.b_succ b !! v)).

  Definition label_of (b : RO.builder) (v : nat) : RO.node :=
    default (RO.nVar 0) (RO.b_label b !! v).

  Lemma succ_of_closed (b : RO.builder) (v : nat) :
    Forall (fun w => w ∈ verts_of b) (succ_of b v).
  Proof.
    apply Forall_forall.
    intros w Hw.
    unfold succ_of in Hw.
    apply elem_of_list_filter in Hw.
    destruct Hw as [_ Hw].
    now apply bool_decide_true in Hw.
  Qed.

  Program Definition graph_of (b : RO.builder) : FiniteDigraph.fin_digraph nat :=
    {| FiniteDigraph.verts := verts_of b;
       FiniteDigraph.succ := succ_of b |}.
  Next Obligation.
    intros b v Hv.
    exact (succ_of_closed b v).
  Qed.

  Definition preproof_of (b : RO.builder) : @Preproof.preproof Judgement Rule nat _ _ :=
    {| Preproof.pp_graph := graph_of b;
       Preproof.pp_label := label_of b;
       Preproof.pp_rule_ok := fun _ _ => I |}.

  Lemma compile_tm_root_label (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    is_Some (RO.b_label b' !! root).
  Proof.
    revert ρ t b root b'.
    induction fuel as [|fuel IH]; intros ρ t b root b' H;
      simpl in H.
    - (* fuel = 0 *)
      destruct (RO.fresh b) as [v0 b0] eqn:Hfresh.
      inversion H; subst.
      unfold RO.put.
      simpl.
      rewrite lookup_insert.
      eexists.
      reflexivity.
    - (* fuel = S fuel *)
      destruct t; try (destruct (RO.fresh b) as [v0 b0] eqn:Hfresh; inversion H; subst;
        unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity).
      all: try (destruct (RO.fresh b) as [v0 b0] eqn:Hfresh;
        (* the remaining cases perform recursive compilation but always end by `put v0 ...` *)
        repeat (destruct (RO.compile_tm fuel _ _ _ ) as [vx bx] eqn:?);
        inversion H; subst; unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity).
      (* tApp case *)
      + (* tApp *)
        destruct (RO.app_view (Term.Syntax.tApp t1 t2)) as [h args] eqn:Hview.
        destruct h.
        * (* head is a variable *)
          destruct (nth_error ρ x) as [[target|]|] eqn:Hnth.
          -- (* backlink case *)
             (* after allocating the backlink vertex we always `put` it *)
             repeat (destruct (RO.compile_tm fuel ρ _ _) as [vx bx] eqn:?);
             repeat (destruct (RO.fresh _) as [vx bx] eqn:?);
             inversion H; subst; unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity.
          -- (* non-backlink *)
             destruct (RO.fresh b) as [v0 b0] eqn:Hfresh.
             repeat (destruct (RO.compile_tm fuel _ _ _ ) as [vx bx] eqn:?);
             inversion H; subst; unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity.
          -- (* non-backlink *)
             destruct (RO.fresh b) as [v0 b0] eqn:Hfresh.
             repeat (destruct (RO.compile_tm fuel _ _ _ ) as [vx bx] eqn:?);
             inversion H; subst; unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity.
        * (* head is not a variable *)
          destruct (RO.fresh b) as [v0 b0] eqn:Hfresh.
          repeat (destruct (RO.compile_tm fuel _ _ _ ) as [vx bx] eqn:?);
          inversion H; subst; unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity.
  Qed.

  Lemma read_off_root_in (t : Term.Syntax.tm) (root : nat) (b : RO.builder) :
    RO.read_off_raw t = (root, b) ->
    root ∈ verts (graph_of b).
  Proof.
    intro H.
    unfold RO.read_off_raw in H.
    apply elem_of_dom.
    apply (compile_tm_root_label (fuel := Term.Syntax.size t) (ρ := [])
             (t := t) (b := RO.empty_builder) (root := root) (b' := b)).
    exact H.
  Qed.

  Definition rooted_preproof_of (t : Term.Syntax.tm)
      : @Preproof.rooted_preproof Judgement Rule nat _ _ :=
    let '(root, b) := RO.read_off_raw t in
    {| Preproof.rpp_proof := preproof_of b;
       Preproof.rpp_root := root;
       Preproof.rpp_root_in := (read_off_root_in t root b eq_refl) |}.
End Packaging.
