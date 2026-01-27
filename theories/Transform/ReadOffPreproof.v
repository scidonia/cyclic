From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap.
From Stdlib Require Import List.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff CyclicRules.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module CR := CyclicRules.

Section Packaging.
  (** Package the raw read-off graph as a rooted preproof whose labels are
      vertex-based judgements.

      This is an incremental correctness step:
      - substitution evidence nodes (`nSubstNil`/`nSubstCons`) are labelled by
        `jSub` judgements and checked by the structural `jSub` rule.
      - all other nodes are labelled by a dummy `jTy` judgement and are accepted
        by a permissive rule (`True`) for now.

      Next step: strengthen `jTy`/`jEq` cases and make `pp_label` produce real
      typing/equality goals.
  *)

  Definition V : Type := nat.

  Definition verts_of (b : RO.builder) : gset V :=
    dom (RO.b_label b).

  Definition succ_of (b : RO.builder) (v : V) : list V :=
    filter (fun w => bool_decide (w ∈ verts_of b))
      (default [] (RO.b_succ b !! v)).

  Definition label_of (b : RO.builder) (v : V) : RO.node :=
    default (RO.nVar 0) (RO.b_label b !! v).

  Definition dummy_type : V := 0.

  Fixpoint sub_ctx (fuel : nat) (b : RO.builder) (sv : V) : list V :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match RO.b_label b !! sv with
        | Some (RO.nSubstNil _) => []
        | Some (RO.nSubstCons _) =>
            match RO.b_succ b !! sv with
            | Some [u; sv_tail] => dummy_type :: sub_ctx fuel' b sv_tail
            | _ => []
            end
        | _ => []
        end
    end.

  Definition shiftV (_n _k : nat) (x : V) : V := x.
  Definition substV (_sv : V) (x : V) : V := x.

  Definition Judgement : Type := CR.judgement (V := V).

  Definition pp_label (b : RO.builder) (v : V) : Judgement :=
    match label_of b v with
    | RO.nSubstNil _ => CR.jSub (V := V) [] v (sub_ctx (RO.b_next b + 1) b v)
    | RO.nSubstCons _ => CR.jSub (V := V) [] v (sub_ctx (RO.b_next b + 1) b v)
    | _ => CR.jTy (V := V) [] v dummy_type
    end.

  Definition Rule (b : RO.builder) (j : Judgement) (premises : list Judgement) : Prop :=
    match j with
    | CR.jSub _ _ _ => CR.rule (V := V) (label_of b) (succ_of b) shiftV substV j premises
    | _ => True
    end.

  Lemma succ_of_closed (b : RO.builder) (v : V) :
    Forall (fun w => w ∈ verts_of b) (succ_of b v).
  Proof.
    apply Forall_forall.
    intros w Hw.
    unfold succ_of in Hw.
    apply filter_In in Hw.
    destruct Hw as [_ Hw].
    now apply bool_decide_true in Hw.
  Qed.

  Program Definition graph_of (b : RO.builder) : FiniteDigraph.fin_digraph V :=
    {| FiniteDigraph.verts := verts_of b;
       FiniteDigraph.succ := succ_of b |}.
  Next Obligation.
    intros b v Hv.
    exact (succ_of_closed b v).
  Qed.

  Lemma pp_rule_ok (b : RO.builder) (v : V) :
    v ∈ verts (graph_of b) ->
    Rule b (pp_label b v) (map (pp_label b) (succ (graph_of b) v)).
  Proof.
    intro Hv.
    unfold Rule.
    unfold pp_label.
    destruct (label_of b v) eqn:Hlbl; simpl; try exact I.
    all: (* substitution vertices *)
      unfold CR.rule; simpl.
      (* The `jSub` rule is a definitional match; our premises are the labels of
         successor vertices, so this closes by computation. *)
      tauto.
  Qed.

  Definition preproof_of (b : RO.builder)
      : @Preproof.preproof Judgement (Rule b) V _ _ :=
    {| Preproof.pp_graph := graph_of b;
       Preproof.pp_label := pp_label b;
       Preproof.pp_rule_ok := fun v Hv => pp_rule_ok b v Hv |}.

  Lemma compile_tm_root_label (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    is_Some (RO.b_label b' !! root).
  Proof.
    revert ρ t b root b'.
    induction fuel as [|fuel IH]; intros ρ t b root b' H;
      simpl in H.
    - destruct (RO.fresh b) as [v0 b0] eqn:Hfresh.
      inversion H; subst.
      unfold RO.put.
      simpl.
      rewrite lookup_insert.
      eexists; reflexivity.
    - destruct t; simpl in H.
      all: try (destruct (RO.fresh b) as [v0 b0] eqn:Hfresh; inversion H; subst;
        unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity).
      (* Remaining constructors call `put` at the returned root. *)
      all: try (repeat (destruct (RO.fresh b) as [v0 b0] eqn:Hfresh); clear Hfresh;
        repeat (destruct (RO.compile_tm fuel _ _ _ ) as [vx bx] eqn:?);
        inversion H; subst; unfold RO.put; simpl; rewrite lookup_insert; eexists; reflexivity).
  Qed.

  Lemma read_off_root_in (t : Term.Syntax.tm) (root : nat) (b : RO.builder) :
    RO.read_off_raw t = (root, b) ->
    root ∈ verts (graph_of b).
  Proof.
    intro H.
    unfold RO.read_off_raw in H.
    apply elem_of_dom.
    apply (compile_tm_root_label (fuel := RO.fuel_tm t) (ρ := [])
             (t := t) (b := RO.empty_builder) (root := root) (b' := b)).
    exact H.
  Qed.

  Definition rooted_preproof_of (t : Term.Syntax.tm)
      : @Preproof.rooted_preproof Judgement (fun j ps => Rule (snd (RO.read_off_raw t)) j ps) V _ _ :=
    let '(root, b) := RO.read_off_raw t in
    {| Preproof.rpp_proof := preproof_of b;
       Preproof.rpp_root := root;
       Preproof.rpp_root_in := (read_off_root_in t root b eq_refl) |}.
End Packaging.
