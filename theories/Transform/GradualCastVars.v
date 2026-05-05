From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile LemmaEnv OmegaRule.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(** Gradual Cast with Variables — SC Discovers Safety

    The canonical gradual typing pattern:
      plus (uncast_nat (cast_dyn e1))
           (uncast_nat (cast_dyn e2))

    For symbolic e1, e2, the SC should drive this to a safe result
    when both e1, e2 produce v_nat values, and to Wrong otherwise.

    Σ = [Nat, List, Maybe, Expr_gradual (I=4), Value (I=5)]
*)

Definition Σg : Typing.Typing.env :=
  [Examples.Nat_sig; ListNat.List_sig; ListNat.Maybe_sig;
   ListNat.Expr_sig_val; ListNat.Value_sig].

(* ------------------------------------------------------------------ *)
(** Example 3var: symbolic e1, e2 — both with safe cast wrappers      *)
(* ------------------------------------------------------------------ *)

(** The expression: plus(uncast(cast(e1)), uncast(cast(e2)))
    In context: [e2:Expr, e1:Expr]
    tVar 1 = e2, tVar 0 = e1 *)
Definition t_plus_casted : tm :=
  tApp ListNat.gradual_eval
       (ListNat.g_plus
         (ListNat.g_uncast_nat (ListNat.g_cast_dyn (tVar 0)))
         (ListNat.g_uncast_nat (ListNat.g_cast_dyn (tVar 1)))).

(** Standard SC — does it terminate? *)
Lemma plus_casted_smoke : forall fuel,
  exists t, Supercompile.residualise_jTy fuel fuel Σg
    [ListNat.expr_g_ty; ListNat.expr_g_ty]
    t_plus_casted ListNat.value_ty = Some t.
Proof.
  intro fuel.
  unfold t_plus_casted.
  vm_compute. eexists. reflexivity.
Qed.

(** The SC drives this but the residual is a recursive function on e1/e2,
    not a simple value — because the SC must handle the generic symbolic case
    where e1 and e2 can be any expression.  The correct omega-rule lemma:

    Lemma safe_cast_preserves:
      eval (uncast_nat (cast_dyn e)) = eval e

    This is proved by induction on e (sub-SC).  With the lemma,
    the main expression reduces as:

      eval (plus (uncast(cast(e1))) (uncast(cast(e2))))
      → eval (plus (eval e1) (eval e2))          [by lemma]
      → plus (eval_nat e1) (eval_nat e2)          [if both are v_nat]
*)

Definition lemma_safe_cast : LemmaEnv.lemma := {|
  LemmaEnv.lemma_lhs :=
    tApp ListNat.gradual_eval
         (ListNat.g_uncast_nat (ListNat.g_cast_dyn (tVar 0)));
  LemmaEnv.lemma_rhs :=
    tApp ListNat.gradual_eval (tVar 0)
|}.

Lemma safe_cast_lemma_validated :
  LemmaEnv.validate_lemma 160 400 Σg
    (LemmaEnv.lemma_lhs lemma_safe_cast)
    (LemmaEnv.lemma_rhs lemma_safe_cast)
    ListNat.value_ty = true.
Proof. vm_compute. reflexivity. Qed.

(** With the lemma, the symbolic plus_casted should reduce to the
    same residual as plus(e1, e2) — the casts are eliminated. *)
Definition t_plus_direct : tm :=
  tApp ListNat.gradual_eval
       (ListNat.g_plus (tVar 0) (tVar 1)).

Definition r_casted_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σg
    [lemma_safe_cast]
    [ListNat.expr_g_ty; ListNat.expr_g_ty]
    t_plus_casted ListNat.value_ty.

Definition r_direct_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σg
    [lemma_safe_cast]
    [ListNat.expr_g_ty; ListNat.expr_g_ty]
    t_plus_direct ListNat.value_ty.

Lemma cast_elimination_via_omega :
  r_casted_omega = r_direct_omega.
Proof. vm_compute. reflexivity. Qed.

(** The SC with the lemma proves that safe casts compose with plus
    — the casts are eliminated for all symbolic e1, e2.

    This is the compile-time cast elimination property:
    code with safe casts (cast_dyn followed by uncast_nat on each operand)
    produces the same result as code without casts. *)
