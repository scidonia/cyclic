From Stdlib Require Import List Bool Arith Utf8.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

(** * Lemma Environment for the Supercompiler

    During driving, the SC may apply proved lemmas as rewrite rules.
    A lemma is a pair [(lhs, rhs)] meaning [lhs ≈_CIU rhs].

    The lemma environment is additive: lemmas are proposed by the LLM,
    validated by a sub-SC run, and then used as left-to-right rewrites.

    SOUNDNESS: lemmas are only added if [supercompile_jTy_tc] succeeds
    on [lhs] and the residual equals [rhs] under [tm_eqb].  This is a
    kernel-checked step — the LLM is untrusted.

    ARCHITECTURE:
    1. [match_ievel sc] — does a lemma's lhs match the current config?
    2. [validate_lemma Σ lhs rhs A] — sub-SC validates the lemma.
    3. [drive_step_with_lemmas Σ lemmas j] — extends [drive_step] with lemma rewrites.
*)

Module SC := Supercompile.
Module Ty := Typing.Typing.

(** A lemma record: lhs ≈ rhs (CIU equivalent). *)
Record lemma : Type := {
  lemma_lhs : tm;
  lemma_rhs : tm;
}.

(** Lemma environment: list of proved lemmas. *)
Definition lemma_env : Type := list lemma.

(** [lemma_env_ok Σ lemmas]: every lemma in the environment has been
    validated — the SC produces a residual equal to [rhs] from [lhs]. *)
Definition lemma_env_ok (Σ : Ty.env) (lemmas : lemma_env) : Prop :=
  Forall
    (fun l =>
       exists fuel_res,
         SC.residualise_jTy 80 200 Σ []
           (lemma_lhs l) (tVar 0) = Some (lemma_rhs l))
    lemmas.

(** [validate_lemma Σ lhs rhs A] tries to validate a single lemma.
    Returns true if the SC run succeeds and produces [rhs]. *)
Definition validate_lemma
    (fuel_sc fuel_res : nat)
    (Σ : Ty.env) (lhs rhs A : tm) : bool :=
  match SC.residualise_jTy fuel_sc fuel_res Σ [] lhs A with
  | None => false
  | Some t => SC.tm_eqb t rhs
  end.

(** [match_lemma lemma config]: does the lemma's lhs appear as a subterm
    of the config's term?  Returns the context (the term with the match
    replaced by a hole) and the substitution needed.

    For now we use a simpler check: exact syntactic match at the root.
    Full subterm matching is future work (requires contextual rewriting). *)
Definition match_lemma_root (l : lemma) (j : SC.config) : option tm :=
  match j with
  | Ty.Cyclic.jTy _ t _ =>
      if SC.tm_eqb t (lemma_lhs l) then Some (lemma_rhs l) else None
  | _ => None
  end.

(** Extend [drive_step] with lemma rewrites:
    if a lemma matches the current config's term, produce a single
    successor with the RHS substituted. *)
Definition drive_step_with_lemmas
    (Σ : Ty.env) (lemmas : lemma_env) (j : SC.config) : list SC.config :=
  let base := SC.drive_step Σ j in
  (* Try each lemma: if it matches at the root, add a rewrite successor *)
  let lemma_succs :=
    flat_map
      (fun l =>
         match match_lemma_root l j with
         | None => []
         | Some rhs =>
             match j with
             | Ty.Cyclic.jTy Γ _ A =>
                 [Ty.Cyclic.jTy Γ rhs A]
             | _ => []
             end
         end)
      lemmas
  in
  base ++ lemma_succs.

(** Full lemma-driven SC: same as [supercompile_cfg_llm] but with
    lemma-aware driving.  This is the entry point for omega-rule proofs. *)
From Cyclic.Transform Require Import LLMOracle.

(** For now, we define a wrapper that uses [LLM.supercompile_cfg_llm]
    with [best_generalize_llm] (AU → speculation → LLM oracle),
    and augments the driving step with lemma rewrites.

    The full integration requires replacing [supercompile_cfg]'s
    [drive_step] call with [drive_step_with_lemmas].  Since that is
    a deep change, we expose a separate entry point. *)

(** Lemma-driven SC top-level: tries to SC [t] with lemma rewrites.
    If the standard SC (with LLM + speculation) produces a residual,
    returns it.  Otherwise, if a lemma is pending, tries again. *)
Definition sc_with_lemmas
    (fuel_sc fuel_res fuel_lemma : nat)
    (Σ : Ty.env) (lemmas : lemma_env)
    (Γ : Ty.ctx) (t A : tm) : option tm :=
  LLM.residualise_jTy_llm fuel_sc fuel_res Σ Γ t A.

(** The current integration point: [sc_with_lemmas] is a placeholder.
    Full integration requires replacing the inner [supercompile_cfg]'s
    [drive_step] with [drive_step_with_lemmas], and providing a lemma
    proposal feedback loop.

    This will be completed when the sub-SC validation loop is implemented
    (Phase 2 of LOGICAL_RELATIONS_PLAN.md). *)
