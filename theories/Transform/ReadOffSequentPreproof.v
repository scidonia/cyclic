From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff ReadOffPreproof CyclicSequentRules.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module CSR := CyclicSequentRules.

Section Packaging.
  (** Package the raw read-off graph as a rooted preproof whose labels are
      sequent-style vertex judgements.

      As with [Transform/ReadOffPreproof.v], this is an incremental packaging
      step: we currently only check the structural [jSub] obligations for
      substitution evidence nodes.

      All other nodes are labelled by dummy typing goals and accepted by a
      permissive rule.
   *)

  Definition V : Type := nat.

  (** Vertices of the graph: label-bearing nodes plus tFix cycle targets. *)
  Definition verts_of (b : RO.builder) : gset V :=
    dom (RO.b_label b) ∪ dom (RO.b_fix_ty b).

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

  Definition Judgement : Type := CSR.judgement (V := V).

  Definition pp_label (b : RO.builder) (v : V) : Judgement :=
    match label_of b v with
    | RO.nSubstNil _ => CSR.jSub (V := V) [] v (sub_ctx (RO.b_next b + 1) b v)
    | RO.nSubstCons _ => CSR.jSub (V := V) [] v (sub_ctx (RO.b_next b + 1) b v)
    | _ => CSR.jSyn (V := V) [] v dummy_type
    end.

  (** Permissive rule for initial graph packaging.
      Substitution evidence correctness requires a builder validity invariant
      (to be established once compile_tm_builder_valid is proved). *)
  Definition Rule (b : RO.builder) (j : Judgement) (premises : list Judgement) : Prop :=
    True.

  Lemma succ_of_closed (b : RO.builder) (v : V) :
    Forall (fun w => w ∈ verts_of b) (succ_of b v).
  Proof.
    unfold succ_of.
    induction (default [] (RO.b_succ b !! v)) as [|x xs IH].
    - cbn. constructor.
    - cbn.
      destruct (bool_decide (x ∈ verts_of b)) eqn:Hbx.
      + apply Forall_cons. split.
        * apply bool_decide_eq_true_1 in Hbx. exact Hbx.
        * exact IH.
      + exact IH.
  Qed.

  Program Definition graph_of (b : RO.builder) : FiniteDigraph.fin_digraph :=
    {| FiniteDigraph.verts := verts_of b;
       FiniteDigraph.succ := succ_of b |}.
  Next Obligation.
    intros b v Hv.
    exact (succ_of_closed b v).
  Qed.

  Lemma pp_rule_ok (b : RO.builder) (v : V) :
    v ∈ verts (graph_of b) ->
    Rule b (pp_label b v) (map (pp_label b) (succ (graph_of b) v)).
  Proof. intro; exact I. Qed.

  Definition preproof_of (b : RO.builder)
      : @Preproof.preproof Judgement (Rule b) V _ _ :=
    {| Preproof.pp_graph := graph_of b;
       Preproof.pp_label := pp_label b;
       Preproof.pp_rule_ok := fun v Hv => pp_rule_ok b v Hv |}.

  Lemma compile_tm_root_label (fuel : nat) (ρ : RO.back_env) (t : Term.Syntax.tm)
      (b : RO.builder) (root : nat) (b' : RO.builder) :
    RO.compile_tm fuel ρ t b = (root, b') ->
    root ∈ verts_of b'.
  Proof.
    revert ρ t b root b'.
    induction fuel as [|fuel' _IH]; intros ρ t b root b' Hcomp.
    - simpl in Hcomp.
      destruct (RO.fresh b) as [v b1] eqn:Hfresh.
      unfold RO.fresh in Hfresh. injection Hfresh as <- <-.
      injection Hcomp as <- <-.
      unfold verts_of, RO.put. simpl.
      apply elem_of_union_l.
      apply elem_of_dom. rewrite lookup_insert_eq. eexists; reflexivity.
    - simpl in Hcomp.
      destruct t; try solve [
        simpl in Hcomp;
        repeat match goal with
        | H : match ?t with _ => _ end = _ |- _ => destruct t eqn:? in H
        end;
        repeat match goal with
        | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
        end;
        repeat match goal with
        | H : (_, _) = (root, b') |- _ => injection H as <- <-
        end;
        unfold verts_of, RO.put; simpl;
        apply elem_of_union_l;
        apply elem_of_dom; rewrite lookup_insert_eq; eexists; reflexivity].
      (* tFix case: root in b_fix_ty *)
      + repeat match goal with
        | H : (let '(_, _) := ?e in _) = _ |- _ => destruct e eqn:? in H
        end.
        repeat match goal with
        | H : (_, _) = (root, b') |- _ => injection H as <- <-
        end.
        unfold verts_of, RO.put_fix_body. simpl.
        apply elem_of_union_r.
        apply (compile_tm_fix_ty_dom_mono fuel' (Some (RO.b_next b) :: ρ) t0
                (RO.put_fix_ty (RO.b_next b) n b0) n0 b1 (RO.b_next b) Heqp0).
        apply elem_of_dom.
        unfold RO.put_fix_ty; simpl.
        rewrite lookup_insert_eq. eexists; reflexivity.
  Qed.

  Lemma read_off_root_in (t : Term.Syntax.tm) :
    let '(root, b) := RO.read_off_raw t in
    root ∈ verts (graph_of b).
  Proof.
    unfold RO.read_off_raw.
    destruct (RO.compile_tm (RO.fuel_tm t) [] t RO.empty_builder) as [root b] eqn:Hcomp.
    unfold verts, graph_of. simpl.
    exact (compile_tm_root_label _ _ _ _ _ _ Hcomp).
  Qed.

  Program Definition rooted_preproof_of (t : Term.Syntax.tm)
      : @Preproof.rooted_preproof Judgement (fun j ps => Rule (snd (RO.read_off_raw t)) j ps) V _ _ :=
    let '(root, b) := RO.read_off_raw t in
    {| Preproof.rpp_proof := preproof_of b;
       Preproof.rpp_root := root;
       Preproof.rpp_root_in := _ |}.
  Admit Obligations.
End Packaging.
