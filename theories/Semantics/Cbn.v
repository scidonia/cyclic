From Stdlib Require Import List Utf8 Relations Relation_Operators.

From Cyclic.Syntax Require Import StrictPos Term.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

(* Call-by-name (weak-head) operational semantics for raw terms.

   We reduce only in:
   - function position of application
   - scrutinee position of case
   - the head of a fix

   Arguments are never evaluated before substitution.
*)

Fixpoint apps (t : tm) (us : list tm) : tm :=
  match us with
  | [] => t
  | u :: us => apps (tApp t u) us
  end.

Inductive step : tm -> tm -> Prop :=
| step_beta A t u :
    step (tApp (tLam A t) u) (subst0 u t)
| step_app1 t t' u :
    step t t' ->
    step (tApp t u) (tApp t' u)
| step_fix A t :
    step (tFix A t) (subst0 (tFix A t) t)
| step_case_scrut I scrut scrut' C brs :
    step scrut scrut' ->
    step (tCase I scrut C brs) (tCase I scrut' C brs)
| step_case_roll I c params recs C brs br :
    branch brs c = Some br ->
    step (tCase I (tRoll I c params recs) C brs)
      (apps br (params ++ recs)).

Definition steps : tm -> tm -> Prop :=
  clos_refl_trans tm step.

Inductive value : tm -> Prop :=
| v_lam A t : value (tLam A t)
| v_roll I c params recs : value (tRoll I c params recs).

(* Neutrals are stuck at the head (no CBN reduction possible). *)
Inductive neutral : tm -> Prop :=
| ne_var x : neutral (tVar x)
| ne_app t u : neutral t -> neutral (tApp t u)
| ne_case I t C brs : neutral t -> neutral (tCase I t C brs).

(* Weak-head normal forms: values or neutrals. *)
Inductive whnf : tm -> Prop :=
| whnf_val v : value v -> whnf v
| whnf_ne t : neutral t -> whnf t.

Definition eval_whnf (t w : tm) : Prop :=
  steps t w ∧ whnf w.

Notation "t ⇓wh w" := (eval_whnf t w) (at level 70).

Definition terminates_to (t v : tm) : Prop :=
  steps t v ∧ value v.

Definition terminates (t : tm) : Prop :=
  ∃ v, terminates_to t v.

CoInductive diverges (t : tm) : Prop :=
| diverges_step t' : step t t' -> diverges t' -> diverges t.
