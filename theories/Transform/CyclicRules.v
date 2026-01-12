From Stdlib Require Import List Arith Utf8.
From stdpp Require Import prelude countable.

From Cyclic.Transform Require Import ReadOff.

Import ListNotations.

Set Default Proof Using "Type".

Module RO := ReadOff.

(**
  Vertex-based judgement + rule system (first cut)

  This file defines the *shape* of the cyclic judgement/rule system over
  vertices, using the node labels produced by `Transform.ReadOff`.

  Design constraints:
  - terms and types are vertices
  - substitutions are explicit evidence vertices (`nSubstNil`/`nSubstCons`)
  - recursion is represented only by cycles/back-links (no `tFix` in the cyclic object)

  This is intentionally a first cut:
  - it fully specifies `jSub` and the backlink typing rule
  - it includes basic `Var`/`Sort`/`Pi`/`Lam`/`App` schemas for `jTy`
  - it includes basic equality rules (`refl/symm/trans`)

  The missing part (planned next): definitional equality via normalization and
  full inductive typing rules (`Ind/Roll/Case`) over vertices.
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
    | _ :: Γ, S x => ctx_lookup Γ x
    end.

  Inductive judgement : Type :=
  | jTy (Γ : ctx) (v A : V)
  | jEq (Γ : ctx) (v w A : V)
  | jSub (Δ : ctx) (sv : V) (Γ : ctx).

  (** Abstract graph-level operations.

      These must be implemented later by a fix-free rewriting semantics.
      They are only used here to state the intended rule schemas.
  *)
  Context (shiftV : nat -> nat -> V -> V).
  Context (substV : V -> V -> V).

  Definition is_sort (v : V) (i : nat) : Prop :=
    label v = RO.nSort i.

  Definition is_pi (v A B : V) : Prop :=
    label v = RO.nPi /\ succ v = [A; B].

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
                premises = [jSub Δ sv_tail Γ'; jTy Δ u (substV sv_tail (shiftV 1 0 A))])
        end

    | jTy Γ v A =>
        match label v with
        | RO.nVar x => premises = [] /\ ctx_lookup Γ x = Some A

        | RO.nSort i =>
            label A = RO.nSort (S i) /\ premises = []

        | RO.nPi =>
            (exists vA vB sI sJ sK i j k,
                succ v = [vA; vB]
                /\ label sK = RO.nSort k
                /\ label sI = RO.nSort i
                /\ label sJ = RO.nSort j
                /\ A = sK
                /\ premises = [jTy Γ vA sI; jTy (vA :: Γ) vB sJ])

        | RO.nLam =>
            (exists vA vt vB vPi sI i,
                succ v = [vA; vt]
                /\ is_pi vPi vA vB
                /\ A = vPi
                /\ label sI = RO.nSort i
                /\ premises = [jTy Γ vA sI; jTy (vA :: Γ) vt vB])

        | RO.nApp =>
            (exists vf va vPi vA vB sv,
                succ v = [vf; va]
                /\ is_pi vPi vA vB
                /\ premises = [jTy Γ vf vPi; jTy Γ va vA; jSub Γ sv (vA :: Γ)]
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
                /\ premises = [jTy Γ0 target A0; jSub Γ sv Γ0]
                /\ A = substV sv A0)
        end

    | jEq Γ v w A =>
        (* Definitional-ish equality: start with structural proof rules.

           Normalization/computation rules will be added later.
        *)
        (premises = [jTy Γ v A] /\ v = w)
        \/ (premises = [jEq Γ w v A])
        \/ (exists m, premises = [jEq Γ v m A; jEq Γ m w A])
    end.
End Rules.
