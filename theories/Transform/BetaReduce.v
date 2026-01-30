From Stdlib Require Import List Utf8 FunctionalExtensionality Relation_Operators.
From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Equiv Require Import CIUJudgement.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Progress Require Import PatternUnification.

Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module PU := PatternUnification.

Definition tm_eqb : tm -> tm -> bool := PU.tm_eqb.

(** One-step call-by-name β-reduction at the head.

    We only contract the redex `(tApp (tLam A t) u)` at the top.
    This matches the CBN semantics, which reduces in function position only.
*)
Definition beta_reduce_once (t : tm) : tm :=
  match t with
  | tApp (tLam A body) u => subst0 u body
  | _ => t
  end.

(** Reduce to weak-head normal form by iterating head reductions.
    Uses fuel to ensure termination. *)
Fixpoint whnf_reduce (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t' := beta_reduce_once t in
      if tm_eqb t t' then t  (* no reduction, already WHNF *)
      else whnf_reduce fuel' t'
  end.

(** Reduce to weak-head normal form, also reducing in head position of applications.
    This keeps reducing the function part of applications. *)
Fixpoint whnf_reduce_deep (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      match t with
      | tApp f u =>
          let f' := whnf_reduce_deep fuel' f in
          let result := tApp f' u in
          let result' := beta_reduce_once result in
          if tm_eqb result result' then result
          else whnf_reduce_deep fuel' result'
      | _ =>
          let t' := beta_reduce_once t in
          if tm_eqb t t' then t
          else whnf_reduce_deep fuel' t'
      end
  end.

(** Full normalization: reduce everywhere including under binders.
    This normalizes the entire term to normal form (not just WHNF). *)
Fixpoint full_normalize (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      (* First reduce to WHNF at the head *)
      let t_whnf := whnf_reduce fuel' t in
      (* Then normalize subterms *)
      match t_whnf with
      | tVar x => tVar x
      | tSort i => tSort i
      | tPi A B => tPi (full_normalize fuel' A) (full_normalize fuel' B)
      | tLam A body => tLam (full_normalize fuel' A) (full_normalize fuel' body)
      | tApp f u =>
          let f_norm := full_normalize fuel' f in
          let u_norm := full_normalize fuel' u in
          (* Try one more beta reduction after normalizing subterms *)
          let app := tApp f_norm u_norm in
          beta_reduce_once app
      | tFix A body => tFix (full_normalize fuel' A) (full_normalize fuel' body)
      | tInd I args => tInd I (map (full_normalize fuel') args)
      | tRoll I c args => tRoll I c (map (full_normalize fuel') args)
      | tCase I scrut C brs =>
          tCase I
                (full_normalize fuel' scrut)
                (full_normalize fuel' C)
                (map (full_normalize fuel') brs)
      end
  end.

Lemma subst0_subst
    (t u : tm) (τ : var -> tm) :
  (subst0 u t).[τ] = subst0 (u.[τ]) (t.[up τ]).
Proof.
  unfold subst0.
  change (t.[u .: ids].[τ] = t.[up τ].[u.[τ] .: ids]).
  rewrite subst_comp.
  rewrite subst_comp.
  assert (Hfun : (u .: ids) >> τ = up τ >> (u.[τ] .: ids)).
  {
    apply functional_extensionality; intros [|x]; cbn.
    - reflexivity.
    - unfold up, Autosubst_Classes.up.
      cbn.
      (* up τ (S x) = rename (+1) (τ x) *)
      unfold rename.
      rewrite rename_subst.
      rewrite subst_comp.
      assert (Hid : ren (+1) >> (u.[τ] .: ids) = ids).
      { apply functional_extensionality; intros [|n]; cbn; reflexivity. }
      rewrite Hid.
      cbn.
      unfold ids.
      rewrite subst_id.
      cbn.
      reflexivity.
  }
  now rewrite Hfun.
Qed.

Lemma terminates_to_beta_step
    (t u : tm) (v : tm) :
  step t u ->
  (terminates_to t v <-> terminates_to u v).
Proof.
  intro Hstep.
  split.
  - intro Hterm.
    eapply terminates_to_steps_prefix.
    + apply steps_step. exact Hstep.
    + exact Hterm.
  - intro Hterm.
    destruct Hterm as [Huv Hv].
    split.
    + eapply steps_trans.
      * apply steps_step. exact Hstep.
      * exact Huv.
    + exact Hv.
Qed.

Theorem ciu_jTy_beta_reduce_once (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  Ty.has_type Σenv Γ t A ->
  CIUJudgement.ciu_jTy Σenv Γ t (beta_reduce_once t) A.
Proof.
  intro Hty.
  destruct t as
    [x|s|A0 B0|A0 t0|t1 t2|A0 t0|I|I c ps rs|I scrut C brs];
    cbn [beta_reduce_once];
    try (apply CIUJudgement.ciu_jTy_of_eq; reflexivity).

  (* t = tApp t1 t2 *)
  destruct t1 as
    [x|s|A1 B1|A1 t3|t3 t4|A1 t3|I1|I1 c1 ps1 rs1|I1 scrut1 C1 brs1];
    cbn [beta_reduce_once];
    try (apply CIUJudgement.ciu_jTy_of_eq; reflexivity).

  (* β-redex case *)
  unfold CIUJudgement.ciu_jTy.
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    (* reduce the substituted term by one β-step, then use prefix lemma *)
    set (lhs := Ty.subst_list σ (tApp (tLam A1 t3) t2)).
    set (rhs := Ty.subst_list σ (subst0 t2 t3)).
    (* show lhs takes one β-step to rhs *)
    assert (Hstep : step lhs rhs).
    {
      subst lhs rhs.
      unfold Ty.subst_list, Ty.subst_sub.
      unfold Typing.Typing.subst_list, Typing.Typing.subst_sub.
      cbn.
      set (τ := Ty.sub_fun (0, σ)).
      (* Rewrite the target into the canonical β-contractum form. *)
      change (Ty.T.subst τ (subst0 t2 t3)) with ((subst0 t2 t3).[τ]).
      rewrite (subst0_subst t3 t2 τ).
      cbn.
      apply step_beta.
    }
    (* Use equivalence of termination across a single step. *)
    apply (proj1 (terminates_to_beta_step lhs rhs v Hstep)).
    exact Hterm.
  - intros Δ σ v Hσ Hvσ Hterm.
    set (lhs := Ty.subst_list σ (tApp (tLam A1 t3) t2)).
    set (rhs := Ty.subst_list σ (subst0 t2 t3)).
    assert (Hstep : step lhs rhs).
    {
      subst lhs rhs.
      unfold Ty.subst_list, Ty.subst_sub.
      unfold Typing.Typing.subst_list, Typing.Typing.subst_sub.
      cbn.
      set (τ := Ty.sub_fun (0, σ)).
      change (Ty.T.subst τ (subst0 t2 t3)) with ((subst0 t2 t3).[τ]).
      rewrite (subst0_subst t3 t2 τ).
      cbn.
      apply step_beta.
    }
    apply (proj2 (terminates_to_beta_step lhs rhs v Hstep)).
    exact Hterm.
Qed.
