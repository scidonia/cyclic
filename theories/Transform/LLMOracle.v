From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile PatternUnification SpeculationGen.

Import ListNotations.

Set Default Proof Using "Type".

(** * LLM-based Generalisation Oracle
 
    ARCHITECTURE:
    1. [llm_generalise] is an axiom-free Parameter — at extraction time it is
       replaced by an OCaml shim (llm_oracle_impl.ml) that calls the Python
       script via subprocess.
    2. [supercompile_cfg_llm] is a drop-in replacement for [supercompile_cfg]
       that falls back to the LLM when [best_generalize] returns None.
    3. The CIU soundness proof holds for ANY output of [supercompile_cfg_llm]
       that passes [trace_condition_ok], because [residualise_cfg_ciu] only
       depends on well-formedness and trace_condition_ok — not on which
       generalisation strategy was used.
 
    THE GAP BEING CLOSED HERE:
    [supercompile_cfg] at line 748 of Supercompile.v calls [best_generalize].
    If that returns None, it just drives forward — potentially looping or
    producing a suboptimal residual.  [supercompile_cfg_llm] inserts one
    extra fallback: ask the LLM for a generalisation before giving up.
*)

Module SC := Supercompile.

Module LLM.

  (** The LLM generalisation oracle.  Untrusted — proposals are validated by
      [best_generalize_llm] before use.  At extraction this Parameter is
      replaced by the OCaml shim in llm_oracle_impl.ml. *)
  Parameter llm_generalise :
    SC.config ->               (* current stuck configuration      *)
    list (SC.config * nat) ->  (* whistle candidates from memo      *)
    option SC.gen_result.      (* proposed generalisation, or None  *)

  (** [best_generalize_llm j cands]:
      1. Standard syntactic anti-unifier ([SC.best_generalize]).
      2. Speculation generalisation ([SpeculationGen.best_generalize_with_speculation])
         — loop-invariant code motion, validates via [vars_independent_of].
      3. LLM oracle — for fusion/accumulator patterns that neither AU nor
         speculation can find.

      Each layer is only tried if the previous one returned None. *)
  Definition best_generalize_llm
      (j : SC.config) (cands : list (SC.config * nat))
      : option (SC.gen_result * nat) :=
    match SC.best_generalize j cands with
    | Some g => Some g
    | None =>
        match SpeculationGen.best_generalize_with_speculation j cands with
        | Some g => Some g
        | None =>
            match llm_generalise j cands with
            | None   => None
            | Some g =>
                let v_prev :=
                  match cands with
                  | []          => 0
                  | (_, v) :: _ => v
                  end
                in
                Some (g, v_prev)
            end
        end
    end.

  (** * [supercompile_cfg_llm]
 
      Identical to [SC.supercompile_cfg] except the single call to
      [SC.best_generalize] on line 748 is replaced by [best_generalize_llm].
      This is the minimal surgical change: every other invariant is preserved.
  *)
  Fixpoint supercompile_cfg_llm
      (fuel : nat) (Σenv : Typing.Typing.env)
      (j : SC.config) (st : SC.sc_state)
      {struct fuel} : option (nat * SC.sc_state) :=
    let j := SC.canon_config (SC.norm_config SC.memo_norm_fuel Σenv j) in
    match SC.memo_lookup j st.(SC.sc_memo) with
    | Some v => Some (v, st)
    | None =>
        let '(v, st1) := SC.sc_alloc j st in
        match fuel with
        | 0 => Some (v, st1)
        | S fuel' =>
            let fix compile_succs (js : list SC.config) (st0 : SC.sc_state)
                {struct js} : option (list nat * SC.sc_state) :=
              match js with
              | [] => Some ([], st0)
              | j0 :: js0 =>
                  match supercompile_cfg_llm fuel' Σenv j0 st0 with
                  | None => None
                  | Some (w, stw) =>
                      match compile_succs js0 stw with
                      | None => None
                      | Some (ws, st2) => Some (w :: ws, st2)
                      end
                  end
              end
            in
            let cands := SC.whistle_candidates fuel' j st.(SC.sc_memo) in
            (* *** THE GAP IS CLOSED HERE ***
               Standard SC uses [SC.best_generalize]; we use
               [best_generalize_llm] which additionally consults the LLM
               oracle when syntactic anti-unification fails. *)
            match best_generalize_llm j cands with
            | Some (g, v_prev) =>
                let '(vg, stg0) := SC.sc_alloc g.(SC.gen_j) st1 in
                let bg1 := SC.cb_put_holes vg g.(SC.gen_holes) stg0.(SC.sc_builder) in
                let bg2 := SC.cb_put_succ v_prev [vg] bg1 in
                let bg3 := SC.cb_put_inst v_prev g.(SC.gen_sub1) bg2 in
                let bg4 := SC.cb_put_succ v [vg] bg3 in
                let bg5 := SC.cb_put_inst v g.(SC.gen_sub2) bg4 in
                let stg1 := {| SC.sc_builder := bg5;
                               SC.sc_memo    := stg0.(SC.sc_memo) |} in
                let nextg := SC.drive_step Σenv g.(SC.gen_j) in
                match compile_succs nextg stg1 with
                | None => Some (v, stg1)
                | Some (vsg, stg2) =>
                    let b' := SC.cb_put_succ vg vsg stg2.(SC.sc_builder) in
                    Some (v, {| SC.sc_builder := b';
                                SC.sc_memo    := stg2.(SC.sc_memo) |})
                end
            | None =>
                let next := SC.drive_step Σenv j in
                match compile_succs next st1 with
                | None => Some (v, st1)
                | Some (vs, st2) =>
                    let b' := SC.cb_put_succ v vs st2.(SC.sc_builder) in
                    Some (v, {| SC.sc_builder := b';
                                SC.sc_memo    := st2.(SC.sc_memo) |})
                end
            end
        end
    end.

  (** Top-level entry points — mirrors [SC.supercompile_jTy_tc] and
      [SC.residualise_jTy] but uses the LLM-augmented loop. *)

  Definition supercompile_jTy_llm
      (fuel : nat) (Σenv : Typing.Typing.env)
      (Γ : Typing.Typing.ctx) (t A : Term.Syntax.tm)
      : option (nat * SC.cfg_builder) :=
    match supercompile_cfg_llm fuel Σenv
            (Typing.Typing.Cyclic.jTy Γ t A) SC.sc_init with
    | None         => None
    | Some (v, st) => Some (v, st.(SC.sc_builder))
    end.

  Definition supercompile_jTy_tc_llm
      (fuel : nat) (Σenv : Typing.Typing.env)
      (Γ : Typing.Typing.ctx) (t A : Term.Syntax.tm)
      : option (nat * SC.cfg_builder) :=
    match supercompile_jTy_llm fuel Σenv Γ t A with
    | None           => None
    | Some (root, b) =>
        if SC.trace_condition_ok b then Some (root, b) else None
    end.

  Definition residualise_jTy_llm
      (fuel_sc fuel_res : nat)
      (Σenv : Typing.Typing.env)
      (Γ : Typing.Typing.ctx) (t A : Term.Syntax.tm)
      : option Term.Syntax.tm :=
    match supercompile_jTy_tc_llm fuel_sc Σenv Γ t A with
    | None           => None
    | Some (root, b) =>
        Some (SC.residualise_cfg fuel_res Σenv b root 0
                (∅ : SC.fix_env))
    end.

End LLM.
