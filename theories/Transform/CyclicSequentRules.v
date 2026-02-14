From Stdlib Require Import List Arith Utf8.
From stdpp Require Import prelude countable.

From Cyclic.Transform Require Import ReadOff.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.

(**
  Cyclic sequent calculus (first cut)

  This file mirrors [Transform/CyclicRules.v] but switches the main typing
  judgement into a (very lightweight) sequent-style, bidirectional presentation:

  - [jSyn Γ v A]  (synthesis) computes a type for vertex [v]
  - [jChk Γ v A]  (checking) verifies vertex [v] against a given type [A]

  The intent is that:
  - introduction forms (e.g. lambdas) are primarily typed in checking mode;
  - elimination forms (e.g. applications) are typed in synthesis mode;
  - "cut"/instantiation is mediated by explicit substitution evidence vertices.

  This is a scaffolding layer: inductive-family rules (Ind/Roll/Case) and a
  proper conversion rule are left schematic for now, just like in
  [Transform/CyclicRules.v].
*)

Section Rules.
  Context {V : Type}.
  Context `{EqDecision V} `{Countable V}.

  Context (label : V -> RO.node).
  Context (succ : V -> list V).

  Definition ctx : Type := list V.

  Fixpoint ctx_lookup (Γ : ctx) (x : nat) : option V :=
    match Γ, x with
    | [], _ => None
    | A :: _, 0 => Some A
    | _ :: Γ', S x' => ctx_lookup Γ' x'
    end.

  Inductive judgement : Type :=
  | jSyn (Γ : ctx) (v A : V)
  | jChk (Γ : ctx) (v A : V)
  | jEq (Γ : ctx) (v w A : V)
  | jSub (Δ : ctx) (sv : V) (Γ : ctx).

  (** Abstract graph-level operations (as in [CyclicRules]). *)
  Context (shiftV : nat -> nat -> V -> V).
  Context (substV : V -> V -> V).

  Definition is_sort (v : V) (i : nat) : Prop :=
    label v = RO.nSort i.

  Definition is_pi (v A B : V) : Prop :=
    label v = RO.nPi /\ succ v = [A; B].

  (** Local rule relation. *)
  Definition rule (j : judgement) (premises : list judgement) : Prop :=
    match j with
    | jSub Δ sv Γ =>
        match Γ with
        | [] =>
            (exists k, label sv = RO.nSubstNil k /\ succ sv = [])
            /\ premises = []
        | A :: Γ' =>
            (exists k u sv_tail,
                label sv = RO.nSubstCons k /\
                succ sv = [u; sv_tail] /\
                premises =
                  [ jSub Δ sv_tail Γ'
                  ; jChk Δ u (substV sv_tail (shiftV 1 0 A))
                  ])
        end

    | jSyn Γ v A =>
        match label v with
        | RO.nVar x => premises = [] /\ ctx_lookup Γ x = Some A

        | RO.nSort i => label A = RO.nSort (S i) /\ premises = []

        | RO.nPi =>
            (exists vA vB sI sJ sK i j k,
                succ v = [vA; vB]
                /\ label sK = RO.nSort k
                /\ label sI = RO.nSort i
                /\ label sJ = RO.nSort j
                /\ A = sK
                /\ premises = [jSyn Γ vA sI; jSyn (vA :: Γ) vB sJ])

        | RO.nLam =>
            (* Lambdas are typed primarily by [jChk]; synthesis is schematic. *)
            True

        | RO.nApp =>
            (exists vf va vPi vA vB sv,
                succ v = [vf; va]
                /\ is_pi vPi vA vB
                /\ premises =
                  [ jSyn Γ vf vPi
                  ; jChk Γ va vA
                  ; jSub Γ sv (vA :: Γ)
                  ]
                /\ A = substV sv vB)

        | RO.nInd _ => True
        | RO.nRoll _ _ _ _ => True
        | RO.nCase _ _ => True

        | RO.nSubstNil _ => False
        | RO.nSubstCons _ => False

        | RO.nBack =>
            (* Backlink typing rule: a recursive call is an instantiation of an
               earlier goal, justified by explicit substitution evidence. *)
            (exists target sv Γ0 A0,
                succ v = [target; sv]
                /\ premises = [jSyn Γ0 target A0; jSub Γ sv Γ0]
                /\ A = substV sv A0)
        end

    | jChk Γ v A =>
        match label v with
        | RO.nLam =>
            (exists vA vt vB sI i,
                succ v = [vA; vt]
                /\ is_pi A vA vB
                /\ label sI = RO.nSort i
                /\ premises = [jSyn Γ vA sI; jChk (vA :: Γ) vt vB])
        | _ =>
            (* A minimal "subsume" rule: check by synthesizing. A proper system
               should add conversion [jEq] and use it here. *)
            premises = [jSyn Γ v A]
        end

    | jEq Γ v w A =>
        (* Definitional-ish equality: start with structural proof rules.

           Normalization/computation rules will be added later.
         *)
        (premises = [jSyn Γ v A] /\ v = w)
        \/ (premises = [jEq Γ w v A])
        \/ (exists m, premises = [jEq Γ v m A; jEq Γ m w A])
    end.
End Rules.
