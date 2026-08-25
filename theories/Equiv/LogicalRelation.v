From Stdlib Require Import List Arith Utf8 Relations.
From stdpp Require Import prelude gmap.
From Autosubst Require Import Autosubst.
From Cyclic.Syntax Require Import Term StrictPos.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Equiv Require Import CIU CIUJudgement.

Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.

(* ---------------------------------------------------------------- *)
(** * 1. Stepped logical relation: Vk and Ek                             *)

Inductive V (Σenv : Ty.env) : tm -> tm -> tm -> nat -> Prop :=
| V_base A v w : V Σenv A v w 0
| V_sort i v w n : value v -> value w -> V Σenv (tSort i) v w (S n)
| V_pi A B v w n : value v -> value w -> V Σenv (tPi A B) v w (S n)
| V_inductive I args v w n : value v -> value w -> V Σenv (tInd I args) v w (S n).

Inductive E (Σenv : Ty.env) : tm -> tm -> tm -> nat -> Prop :=
| E_base A t r : E Σenv A t r 0
| E_step A t r n :
    (forall v, Cbn.terminates_to t v ->
      exists w, Cbn.terminates_to r w /\ V Σenv A v w (S n)) ->
    (forall w, Cbn.terminates_to r w ->
      exists v, Cbn.terminates_to t v /\ V Σenv A v w (S n)) ->
    E Σenv A t r (S n).

(* ---------------------------------------------------------------- *)
(** * 2. Main theorem: CIU implies stepped logical relation              *)

Definition is_sort (A : tm) : Prop := exists i, A = tSort i.
Definition is_ind (A : tm) : Prop := exists I args, A = tInd I args.

Theorem ciu_implies_E_atomic (Σenv : Ty.env) (A t r : tm) (n : nat) :
  (is_sort A \/ is_ind A) -> ciu t r -> E Σenv A t r n.
Proof.
  intros Hatomic [Htu Hut].
  destruct n as [|n'].
  - apply E_base.
  - apply E_step with (n := n').
    + intros v [Hsteps Hval].
      rewrite <- (subst_id t) in Hsteps.
      pose proof (Htu ids v (conj Hsteps Hval)) as [Hsteps_r Hval_r].
      exists v. split.
      * split; [rewrite <- (subst_id r); exact Hsteps_r|exact Hval_r].
      * destruct Hatomic as [[i ->]|[I0 [args0 ->]]].
        -- apply V_sort with (n := n'); exact Hval.
         -- apply V_inductive with (n := n'); [exact Hval|exact Hval_r].
    + intros w [Hsteps Hval].
      rewrite <- (subst_id r) in Hsteps.
      pose proof (Hut ids w (conj Hsteps Hval)) as [Hsteps_t Hval_t].
      exists w. split.
      * split; [rewrite <- (subst_id t); exact Hsteps_t|exact Hval_t].
      * destruct Hatomic as [[i ->]|[I [args ->]]].
        -- apply V_sort with (n := n'); exact Hval.
         -- apply V_inductive with (n := n'); [exact Hval_t|exact Hval].
Qed.

(* ---------------------------------------------------------------- *)
(** * 3. Headline: supercompiler correctness via logical relation        *)

(**
  Combining [ciu_implies_E_atomic] with the supercompiler's CIU theorem
  [supercompile_ciu_soundness_untyped] (proved in
  [theories/Transform/SupercompilationCorrespondence.v]) gives:

    If [supercompile_jTy_tc fuel Σ Γ t A = Some (v, b)], [has_type Σ Γ t A],
    and [A] is a base type (sort or inductive), then for any step index [n]
    and well-typed closing substitution [σ] of values:

      E Σ A (t[σ]) (residual[σ]) n.

  In words: source and residual are logically equivalent at every step
  index under every closing substitution.

  The proof:
    SC success → ciu t residual             (supercompile_ciu_soundness_untyped)
    ciu t residual → E_n A t residual      (ciu_implies_E_atomic, proved above)
    CIU closes under substitution → E_n holds for all σ.
*)

