From Stdlib Require Import List Utf8 Relations Relation_Operators Vectors.Fin Program.Equality.

From Cyclic.Syntax Require Import StrictPos Term.

Import ListNotations.
Import StrictPos.
Import Term.Syntax.

Set Default Proof Using "Type".

(* Call-by-name (weak-head) operational semantics for raw terms.

   This is a small-step semantics that only reduces in:
   - the function position of an application
   - the scrutinee position of a case
   - the top-level of a fix

   Arguments are never evaluated before substitution.
*)

Fixpoint enumFin (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n' => Fin.F1 :: map Fin.FS (enumFin n')
  end.

Fixpoint apps (t : tm) (us : list tm) : tm :=
  match us with
  | [] => t
  | u :: us => apps (tApp t u) us
  end.

Definition roll_params (Σ : ind_sig ty) (s : Shape Σ) (params : ParamPos Σ s -> tm) : list tm :=
  map params (enumFin (param_arity Σ s)).

Definition roll_args (Σ : ind_sig ty) (s : Shape Σ) (k : Pos Σ s -> tm) : list tm :=
  map k (enumFin (arity Σ s)).

Fixpoint shift (d : nat) (c : nat) (t : tm) : tm :=
  match t with
  | tVar x => if Nat.ltb x c then tVar x else tVar (x + d)
  | tLam A t => tLam A (shift d (S c) t)
  | tApp t u => tApp (shift d c t) (shift d c u)
  | tFix A t => tFix A (shift d (S c) t)
  | tRoll Σ s params k =>
      tRoll Σ s
        (fun i => shift d c (params i))
        (fun j => shift d c (k j))
  | tCase Σ scrut C br =>
      tCase Σ (shift d c scrut) C (fun s => shift d c (br s))
  end.

Definition up (σ : nat -> tm) : nat -> tm :=
  fun x =>
    match x with
    | 0 => tVar 0
    | S x => shift 1 0 (σ x)
    end.

Fixpoint subst (σ : nat -> tm) (t : tm) : tm :=
  match t with
  | tVar x => σ x
  | tLam A t => tLam A (subst (up σ) t)
  | tApp t u => tApp (subst σ t) (subst σ u)
  | tFix A t => tFix A (subst (up σ) t)
  | tRoll Σ s params k =>
      tRoll Σ s
        (fun i => subst σ (params i))
        (fun j => subst σ (k j))
  | tCase Σ scrut C br =>
      tCase Σ (subst σ scrut) C (fun s => subst σ (br s))
  end.

Definition subst0 (u : tm) (t : tm) : tm :=
  subst (fun x => match x with 0 => u | S x => tVar x end) t.

Inductive step : tm -> tm -> Prop :=
| step_beta A t u :
    step (tApp (tLam A t) u) (subst0 u t)
| step_app1 t t' u :
    step t t' ->
    step (tApp t u) (tApp t' u)
| step_fix A t :
    step (tFix A t) (subst0 (tFix A t) t)
| step_case_scrut Σ scrut scrut' C br :
    step scrut scrut' ->
    step (tCase Σ scrut C br) (tCase Σ scrut' C br)
| step_case_roll Σ s params k C br :
    step (tCase Σ (tRoll Σ s params k) C br)
      (apps (br s) (roll_params Σ s params ++ roll_args Σ s k)).

Definition steps : tm -> tm -> Prop :=
  clos_refl_trans tm step.

Inductive value : tm -> Prop :=
| v_lam A t : value (tLam A t)
| v_roll Σ s params k : value (tRoll Σ s params k).

(* Neutrals are stuck at the head (no CBN reduction possible). *)
Inductive neutral : tm -> Prop :=
| ne_var x : neutral (tVar x)
| ne_app t u : neutral t -> neutral (tApp t u)
| ne_case Σ t C br : neutral t -> neutral (tCase Σ t C br).

(* Weak-head normal forms: values or neutrals. *)
Inductive whnf : tm -> Prop :=
| whnf_val v : value v -> whnf v
| whnf_ne t : neutral t -> whnf t.

(* Explicit weak-head evaluation: reduce to a WHNF. *)
Definition eval_whnf (t w : tm) : Prop :=
  steps t w ∧ whnf w.

Notation "t ⇓wh w" := (eval_whnf t w) (at level 70).

Definition terminates_to (t v : tm) : Prop :=
  steps t v ∧ value v.

Definition terminates (t : tm) : Prop :=
  ∃ v, terminates_to t v.

CoInductive diverges (t : tm) : Prop :=
| diverges_step t' : step t t' -> diverges t' -> diverges t.

Lemma value_no_step (v v' : tm) :
  value v -> step v v' -> False.
Proof.
  intros Hv Hstep.
  inversion Hv; subst; inversion Hstep.
Qed.

Lemma neutral_no_step (t t' : tm) :
  neutral t -> step t t' -> False.
Proof.
  intro Hn.
  revert t'.
  induction Hn as [x|t u Ht IH|Σ t C br Ht IH]; intro t'; intro Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + inversion Ht.
    + eapply IH; eauto.
  - inversion Hstep; subst.
    + eapply IH; eauto.
    + inversion Ht.
Qed.

Lemma whnf_no_step (t t' : tm) :
  whnf t -> step t t' -> False.
Proof.
  intros Hwh Hstep.
  inversion Hwh; subst.
  - exact (value_no_step _ _ H Hstep).
  - exact (neutral_no_step _ _ H Hstep).
Qed.

(* Determinism of call-by-name stepping. *)
Lemma step_deterministic (t t1 t2 : tm) :
  step t t1 -> step t t2 -> t1 = t2.
Proof.
  intro H1.
  revert t2.
  induction H1 as
    [A t u
    | t t' u Htt' IH
    | A t
    | Σ scrut scrut' C br Hscrut IH
    | Σ s params k C br];
    intro t2; intro H2.
  - inversion H2; subst; try reflexivity; try discriminate.
    exfalso.
    match goal with
    | H : step (tLam _ _) _ |- _ => eapply value_no_step; [apply v_lam|exact H]
    end.
  - inversion H2; subst; try discriminate.
    { exfalso.
      match goal with
      | H : step (tLam _ _) _ |- _ => eapply value_no_step; [apply v_lam|exact H]
      end. }
    { f_equal. eapply IH; eauto. }
  - inversion H2; subst; reflexivity.
  - inversion H2; subst; try discriminate.
    { (* case-scrut vs case-scrut *)
      repeat match goal with
      | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
      end.
      match goal with
      | H : step scrut ?u |- _ => pose proof (IH _ H) as ->
      end.
      reflexivity. }
    { (* case-scrut vs case-roll is impossible: scrut is a roll, but rolls don't step *)
      exfalso.
      eapply value_no_step.
      - apply v_roll.
      - exact Hscrut. }
  - inversion H2; subst; try discriminate.
    { (* case-roll vs case-scrut is impossible: rolls don't step *)
      exfalso.
      match goal with
      | H : step (tRoll _ _ _ _) _ |- _ => eapply value_no_step; [apply v_roll|exact H]
      end. }
    { (* case-roll vs case-roll *)
      repeat match goal with
      | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
      end.
      reflexivity. }
Qed.

(* A helper for reasoning about multi-step reductions. *)
Lemma steps_eq_or_step (t u : tm) :
  steps t u -> t = u ∨ ∃ t', step t t' ∧ steps t' u.
Proof.
  intro H.
  induction H.
  - (* rt_step *)
    right. exists y. split; [exact H|apply rt_refl].
  - (* rt_refl *)
    left. reflexivity.
  - (* rt_trans *)
    destruct IHclos_refl_trans1 as [->|[t' [Ht' Ht'y]]].
    + exact IHclos_refl_trans2.
    + right. exists t'. split.
      * exact Ht'.
      * eapply rt_trans; eauto.
Qed.

Lemma whnf_stuck (w u : tm) :
  whnf w -> steps w u -> u = w.
Proof.
  intros Hwh Hwu.
  destruct (steps_eq_or_step _ _ Hwu) as [->|[w' [Hwstep _]]].
  - reflexivity.
  - exfalso. exact (whnf_no_step _ _ Hwh Hwstep).
Qed.

Lemma steps_compare (t u v : tm) :
  steps t u -> steps t v -> steps u v ∨ steps v u.
Proof.
  intro Htu.
  revert v.
  induction Htu; intro v; intro Htv.
  - (* rt_step *)
    destruct (steps_eq_or_step _ _ Htv) as [Heq|[t' [Ht' Ht'v]]].
    + subst. right. apply rt_step. exact H.
    + assert (t' = y) by (eapply step_deterministic; eauto).
      subst t'. left. exact Ht'v.
  - (* rt_refl *)
    left. exact Htv.
  - (* rt_trans *)
    specialize (IHHtu1 _ Htv) as [Hyv|Hvy].
    + exact (IHHtu2 _ Hyv).
    + right. eapply rt_trans; eauto.
Qed.

Theorem eval_whnf_deterministic (t w1 w2 : tm) :
  t ⇓wh w1 -> t ⇓wh w2 -> w1 = w2.
Proof.
  intros [Ht1 Hw1] [Ht2 Hw2].
  destruct (steps_compare _ _ _ Ht1 Ht2) as [H12|H21].
  - symmetry. exact (whnf_stuck _ _ Hw1 H12).
  - exact (whnf_stuck _ _ Hw2 H21).
Qed.

(* Big-step weak-head evaluation (inductive), equivalent to ⇓wh. *)
Inductive eval_whnf_big : tm -> tm -> Prop :=
| ewhnf_done w : whnf w -> eval_whnf_big w w
| ewhnf_step t t' w : step t t' -> eval_whnf_big t' w -> eval_whnf_big t w.

Lemma eval_whnf_big_sound (t w : tm) :
  eval_whnf_big t w -> t ⇓wh w.
Proof.
  intro He.
  induction He as [w Hwh|t t' w Hstep He IH].
  - split.
    + apply rt_refl.
    + exact Hwh.
  - destruct IH as [Ht'w Hwh].
    split.
    + eapply rt_trans.
      * apply rt_step. exact Hstep.
      * exact Ht'w.
    + exact Hwh.
Qed.

Lemma eval_whnf_big_of_steps (t0 u w : tm) :
  steps t0 u -> eval_whnf_big u w -> eval_whnf_big t0 w.
Proof.
  intro Htu.
  revert w.
  dependent induction Htu; intros w He.
  - (* rt_step *) exact (ewhnf_step _ _ _ H He).
  - (* rt_refl *) exact He.
  - (* rt_trans *)
    apply IHHtu1.
    apply IHHtu2.
    exact He.
Qed.

Lemma eval_whnf_big_complete (t w : tm) :
  t ⇓wh w -> eval_whnf_big t w.
Proof.
  intros [Htw Hwh].
  apply (eval_whnf_big_of_steps t w w Htw).
  exact (ewhnf_done w Hwh).
Qed.

Theorem eval_whnf_big_deterministic (t w1 w2 : tm) :
  eval_whnf_big t w1 -> eval_whnf_big t w2 -> w1 = w2.
Proof.
  intros H1 H2.
  apply (eval_whnf_deterministic t w1 w2);
    apply eval_whnf_big_sound; assumption.
Qed.
