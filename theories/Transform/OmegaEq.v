From Stdlib Require Import List Bool Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import
     Supercompile LemmaEnv LemmaProposer LLMOracle.
Import ListNotations. Import Term.Syntax.
Set Default Proof Using "Type".

(** Omega Rule Equation Prover

    Given two terms t1, t2 in the same context Γ with type A,
    tries to prove t1 = t2 by lemma-driven supercompilation.

    Algorithm:
      1. SC both sides with lemma_env
      2. If residuals are equal (tm_eqb), done.
      3. Else: call LLM to propose a lemma that bridges the gap
      4. Validate lemma via sub-SC (trace_condition_ok)
      5. If valid, add to lemma_env and retry (go to 1)
      6. If max_retries exceeded or no lemma, return false

    This is the omega rule as an equational decision procedure:
    each lemma discovered is a cut formula that makes the two sides
    converge to the same normal form under driving.
*)

Module OmegaEq.

  Module Ty := Typing.Typing.
  Module LLM := LLMOracle.LLM.

  (** Lemma-driven SC for a single term *)

  Fixpoint lemma_driven_supercompile_cfg
      (fuel : nat) (Σenv : Ty.env) (lemmas : LemmaEnv.lemma_env)
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
                  match lemma_driven_supercompile_cfg fuel' Σenv lemmas j0 st0 with
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
            match LLM.best_generalize_llm j cands with
            | Some (g, v_prev) =>
                let '(vg, stg0) := SC.sc_alloc g.(SC.gen_j) st1 in
                let bg1 := SC.cb_put_holes vg g.(SC.gen_holes) stg0.(SC.sc_builder) in
                let bg2 := SC.cb_put_succ v_prev [vg] bg1 in
                let bg3 := SC.cb_put_inst v_prev g.(SC.gen_sub1) bg2 in
                let bg4 := SC.cb_put_succ v [vg] bg3 in
                let bg5 := SC.cb_put_inst v g.(SC.gen_sub2) bg4 in
                let stg1 := {| SC.sc_builder := bg5;
                               SC.sc_memo    := stg0.(SC.sc_memo) |} in
                let nextg := LemmaEnv.drive_step_with_lemmas Σenv lemmas g.(SC.gen_j) in
                match compile_succs nextg stg1 with
                | None => Some (v, stg1)
                | Some (vsg, stg2) =>
                    let b' := SC.cb_put_succ vg vsg stg2.(SC.sc_builder) in
                    Some (v, {| SC.sc_builder := b';
                                SC.sc_memo    := stg2.(SC.sc_memo) |})
                end
            | None =>
                let next := LemmaEnv.drive_step_with_lemmas Σenv lemmas j in
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

  Definition lemma_driven_residualise
      (fuel_sc fuel_res : nat) (Σenv : Ty.env)
      (lemmas : LemmaEnv.lemma_env)
      (Γ : Ty.ctx) (t A : tm) : option tm :=
    match lemma_driven_supercompile_cfg fuel_sc Σenv lemmas
            (Ty.Cyclic.jTy Γ t A) SC.sc_init with
    | None => None
    | Some (root, st) =>
        let b := st.(SC.sc_builder) in
        if SC.trace_condition_ok b then
          Some (SC.residualise_cfg fuel_res Σenv b root 0 (∅ : SC.fix_env))
        else None
    end.

  (** Test whether two terms' residuals are equal under lemma-driven SC *)
  Definition residuals_equal
      (fuel_sc fuel_res : nat) (Σenv : Ty.env)
      (lemmas : LemmaEnv.lemma_env)
      (Γ : Ty.ctx) (t1 t2 A : tm) : bool :=
    match lemma_driven_residualise fuel_sc fuel_res Σenv lemmas Γ t1 A,
          lemma_driven_residualise fuel_sc fuel_res Σenv lemmas Γ t2 A with
    | Some r1, Some r2 => SC.tm_eqb r1 r2
    | _, _ => false
    end.

  (** The equation prover: tries to prove t1 = t2 by discovering lemmas *)
  Fixpoint prove_equation
      (max_retries fuel_sc fuel_res : nat)
      (Σenv : Ty.env) (lemmas : LemmaEnv.lemma_env)
      (Γ : Ty.ctx) (t1 t2 A : tm)
      {struct max_retries} : bool :=
    match max_retries with
    | 0 => residuals_equal fuel_sc fuel_res Σenv lemmas Γ t1 t2 A
    | S max_retries' =>
        if residuals_equal fuel_sc fuel_res Σenv lemmas Γ t1 t2 A then true
        else
          let j1 := Ty.Cyclic.jTy Γ t1 A in
          let j2 := Ty.Cyclic.jTy Γ t2 A in
          match LLMLemma.llm_propose_lemma j1 j2 [] with
          | None => false
          | Some l =>
              (* Validate lemma *)
              let l_ok := LemmaEnv.validate_lemma fuel_sc fuel_res Σenv
                            (LemmaEnv.lemma_lhs l) (LemmaEnv.lemma_rhs l) A in
              if l_ok then
                prove_equation max_retries' fuel_sc fuel_res Σenv
                  (l :: lemmas) Γ t1 t2 A
              else false
          end
    end.

End OmegaEq.
