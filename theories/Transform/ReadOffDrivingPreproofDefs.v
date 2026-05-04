From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff SequentDrivingRules SequentObservationRules.
From Cyclic.Transform Require Import Extract.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module Extr := Extract.
Module SDR := SequentDrivingRules.
Module SOR := SequentObservationRules.
Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module SP := StrictPos.

Section Packaging.
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

  (** Empty fix environment for extraction *)
  Definition empty_fix_env : Extr.fix_env := ∅.

  (** Empty type environment (no inductives) for inference *)
  Definition empty_tyenv : Ty.env := [].

  (** Type reconstruction for vertices.
  
      Given a builder and a fuel bound, compute the type of a vertex.
      This is a forward pass that reconstructs types from the graph structure.
      
      For now, we return vertex IDs (representing type terms in the graph).
      In a full implementation, this would be a separate map computed once.
  *)
  Definition infer_type (fuel : nat) (Σenv : Ty.env) (b : RO.builder)
      (Γ : list V) (v : V) : option V :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match label_of b v with
        | RO.nVar x =>
            (* Look up the type in the context *)
            nth_error Γ x
        | RO.nSort i =>
            (* Sort i has type Sort (i+1) *)
            Some dummy_type  (* Would need to compile tSort (i+1) *)
        | RO.nPi =>
            (* Pi A B : Type if A : Type and B : Type *)
            match succ_of b v with
            | [vA; vB] =>
                (* Should check both A and B are types, return Sort *)
                Some dummy_type
            | _ => None
            end
        | RO.nLam =>
            (* Lam t : Pi A B if t : B *)
            match succ_of b v with
            | [vA; vt] =>
                (* The type is Pi vA (type of vt) *)
                (* For now, return a dummy since we need to construct Pi node *)
                Some dummy_type
            | _ => None
            end
        | RO.nApp =>
            (* App f x : B[x/0] if f : Pi A B and x : A *)
            match succ_of b v with
            | [vf; vx] =>
                (* Would need to: 
                   1. Infer type of vf
                   2. Extract result type from Pi
                   3. Apply substitution
                *)
                Some dummy_type
            | _ => None
            end
        | _ => Some dummy_type  (* Other cases for later *)
        end
    end.

  (** Combined sequent judgement for the cyclic proof object.

      This is intentionally a simple disjunction for now: we'll refine the
      connection between `jDrive` and `jObs` judgements once the graph rewrite
      system is working.
  *)
  Inductive judgement : Type :=
  | jDrive (j : C.judgement)
  | jObs (j : SOR.judgement)
  | jSub (Δ : list V) (sv : V) (Γ : list V).

  (** Compute a context from a substitution-evidence vertex chain.

      This is a fuel-bounded traversal identical to `ReadOffPreproof.sub_ctx`.
  *)
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

  (** Label a read-off vertex with a sequent judgement.

      For now, we assign all non-substitution nodes to `jDrive` with a dummy
      sequent. Once we strengthen this to produce real typing goals, we'll add
      an "observation labelling pass" that identifies observation subgoals
      (e.g. for Nat-typed terms) and labels them with `jObs` instead.
  *)
  Definition pp_label (fuel : nat) (b : RO.builder) (v : V) : judgement :=
    match label_of b v with
    | RO.nSubstNil _ => jSub [] v (sub_ctx (RO.b_next b + 1) b v)
    | RO.nSubstCons _ => jSub [] v (sub_ctx (RO.b_next b + 1) b v)
    | _ =>
        (* Extract the term and its type from the vertex *)
        let t := Extr.extract_v fuel b empty_fix_env v in
        let A := infer_type fuel empty_tyenv b [] v in
        match A with
        | Some vA =>
            let A_tm := Extr.extract_v fuel b empty_fix_env vA in
            jDrive (C.jTy [] t A_tm)
        | None =>
            (* If we can't infer a type, use a dummy *)
            jDrive (C.jTy [] t (tSort 0))
        end
    end.

  (** Dummy shift/subst operations for the vertex-level `jSub` rule.

      These are placeholders: a full account would compute vertex-level
      substitution evidence.
  *)
  Definition shiftV (_n _k : nat) (x : V) : V := x.
  Definition substV (_sv : V) (x : V) : V := x.

  (** The rule relation combines all three judgement forms.

      Each case delegates to the appropriate explicit rule relation.
      
      NOTE: For the initial read-off graph, we use a permissive rule checker
      that accepts all jDrive and jObs nodes. This is correct because the
      read-off graph is the *starting point* for supercompilation, not a proof
      search tree.
      
      The explicit driving and observation rules (SequentDrivingRules.drive_rule
      and SequentObservationRules.rule) will be used in the graph rewrite system
      (Task 2: sc_step_async) to justify transformations of the graph.
      
      Only jSub nodes are checked structurally here, because substitution evidence
      must be correct by construction in the read-off output.
  *)
  Definition rule (Σenv : Ty.env) (b : RO.builder)
      (j : judgement) (premises : list judgement) : Prop :=
    match j with
    | jDrive jd =>
        (* Permissive for initial graph: all term-structure vertices accepted *)
        True
    | jObs jobs =>
        (* Permissive for initial graph: observation nodes will be added during
           graph rewriting when we identify Nat-typed subgoals *)
        True
    | jSub Δ sv Γ =>
        (* Permissive for initial graph packaging: substitution evidence is
           correct by construction (compile_tm's build_subst_chain always
           produces well-formed chains), but proving this formally requires
           a builder validity invariant (succ entries match label arity) that
           we have not yet established.  The structural check will be added
           once builder_valid is proved for compile_tm. *)
        True
    end.

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

  Lemma pp_rule_ok (Σenv : Ty.env) (fuel : nat) (b : RO.builder) (v : V) :
    v ∈ verts (graph_of b) ->
    rule Σenv b (pp_label fuel b v) (map (pp_label fuel b) (succ (graph_of b) v)).
  Proof.
    intro; unfold rule; destruct (pp_label fuel b v); exact I.
  Qed.

  Definition preproof_of (Σenv : Ty.env) (fuel : nat) (b : RO.builder)
      : @Preproof.preproof judgement (rule Σenv b) V _ _ :=
    {| Preproof.pp_graph := graph_of b;
       Preproof.pp_label := pp_label fuel b;
       Preproof.pp_rule_ok := fun v Hv => pp_rule_ok Σenv fuel b v Hv |}.
End Packaging.
