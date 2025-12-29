From Stdlib Require Import List Utf8 Relations Relation_Operators Vectors.Fin.

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

Definition roll_params (Σ : ind_sig) (s : Shape Σ) (params : ParamPos Σ s -> tm) : list tm :=
  map params (enumFin (param_arity Σ s)).

Definition roll_args (Σ : ind_sig) (s : Shape Σ) (k : Pos Σ s -> tm) : list tm :=
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
  | tCase Σ scrut br =>
      tCase Σ (shift d c scrut) (fun s => shift d c (br s))
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
  | tCase Σ scrut br =>
      tCase Σ (subst σ scrut) (fun s => subst σ (br s))
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
| step_case_scrut Σ scrut scrut' br :
    step scrut scrut' ->
    step (tCase Σ scrut br) (tCase Σ scrut' br)
| step_case_roll Σ s params k br :
    step (tCase Σ (tRoll Σ s params k) br)
      (apps (br s) (roll_params Σ s params ++ roll_args Σ s k)).

Definition steps : tm -> tm -> Prop := clos_refl_trans tm step.

Inductive value : tm -> Prop :=
| v_lam A t : value (tLam A t)
| v_roll Σ s params k : value (tRoll Σ s params k).

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

Lemma steps_refl (t : tm) : steps t t.
Proof.
  apply rt_refl.
Qed.

Lemma steps_step (t t' : tm) : step t t' -> steps t t'.
Proof.
  intro H.
  apply rt_step.
  exact H.
Qed.
