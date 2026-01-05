From Stdlib Require Import List Arith Utf8.
From stdpp Require Import prelude countable.

From Cyclic.Preproof Require Import Preproof.

Import ListNotations.

Set Default Proof Using "Type".

(**
  Vertex-level cyclic term language + substitution evidence (spec)

  This file is a *specification* of the data we want for the next milestone:

  - terms and types are represented uniformly as vertices in a cyclic graph
  - `tFix` is forbidden everywhere inside the cyclic proof object
  - recursion is represented only by proof cycles/back-links
  - back-links must carry explicit substitution evidence via `Subst` vertices

  This module type introduces no axioms; it only specifies required shapes.
*)

Module Type CYCLIC_VERTEX_SPEC.
  (** Vertices used to represent terms, types, substitutions. *)
  Parameter V : Type.

  Parameter V_EqDecision : EqDecision V.
  Existing Instance V_EqDecision.

  Parameter V_Countable : Countable V.
  Existing Instance V_Countable.

  (** Node labels: introduction schemas.

      No constructor corresponds to `tFix`.
  *)
  Inductive node : Type :=
  | nVar (x : nat)
  | nSort (i : nat)
  | nPi
  | nLam
  | nApp
  | nInd (ind : nat)
  | nRoll (ind ctor nparams nrecs : nat)
  | nCase (ind nbrs : nat)
  | nSubst (k : nat) (nargs : nat)
  | nBack.

  (** Underlying cyclic term graph.

      `succ v` lists the immediate children of node `v`.
      For `nSubst k nargs`, `succ v` is the argument list.
      For `nBack`, `succ v` has the form `target :: sv :: args`.
  *)
  Parameter label : V -> node.
  Parameter succ : V -> list V.

  (** Contexts and substitution vertices. *)
  Definition ctx : Type := list V.

  (** Judgements.

      Types are vertices too, hence `jTy Γ v A` with `A : V`.
  *)
  Inductive judgement : Type :=
  | jTy (Γ : ctx) (v A : V)
  | jEq (Γ : ctx) (v w A : V)
  | jSub (Δ : ctx) (sv : V) (Γ : ctx).

  (** Graph-level shifting/substitution operations.

      These are required for typing substitutions and for definitional-ish
      equality. They must be defined without introducing any `tFix`.

      The intended meaning is:
      - `shiftV 1 0 A` is the type `A` under one new binder
      - `substV sv t` applies the substitution encoded by `sv` to vertex `t`

      The concrete implementation will operate by graph rewriting and by
      composing back-links rather than unfolding.
  *)
  Parameter shiftV : nat -> nat -> V -> V.
  Parameter substV : V -> V -> V.

  (** Local rule relation.

      This should mirror the CIC typing/equality/substitution rules, but over
      vertices.

      The critical requirement for this step: `jSub` is checked structurally
      against `nSubst k nargs` nodes.
  *)
  Parameter rule : judgement -> list judgement -> Prop.

  Definition preproof : Type :=
    @Preproof.preproof judgement rule V _ _.

  Definition rooted_preproof : Type :=
    @Preproof.rooted_preproof judgement rule V _ _.

  (** Invariant: the cyclic object is fix-free.

      Since we do not represent raw terms, this is a structural invariant on
      `node` and on the implementations of `shiftV`/`substV`.
  *)
  Parameter fix_free : Prop.

  (** Intended `jSub` rule schema (to be implemented):

      If `label sv = nSubst k nargs` and `succ sv = σ`, then `jSub Δ sv Γ`
      checks that:
      - `length σ = length Γ`
      - each argument vertex is well-typed in Δ at the appropriately shifted
        and substituted type.

      This is the vertex-level analogue of `Typing.has_subst`.
  *)
End CYCLIC_VERTEX_SPEC.
