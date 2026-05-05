From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import
     Supercompile LemmaEnv OmegaRule.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  Gradual Typing Benchmark: Cast Safety via Omega Rule

  A language with explicit casts:
    Value ::= v_nat(n) | v_dyn(v) | v_wrong   (I=5)
    Expr  ::= const(n) | plus(e1,e2) | cast_dyn(e) | uncast_nat(e)  (I=4)

  Semantics:
    cast_dyn(n)  → v_dyn(v_nat n)   — wraps a Nat as Dyn
    uncast_nat(v_dyn(v_nat n)) → v_nat n — uncast succeeds
    uncast_nat(v_nat n)       → v_wrong   — can't uncast a plain Nat

  Property (omega rule):
    eval (uncast_nat (cast_dyn e)) = eval e
    (on all e where eval e produces v_nat)

  This requires the lemma:
    eval (cast_dyn e) = v_dyn(v_nat (eval_nat e))
    (where eval_nat extracts the nat from v_nat)

  The standard SC drives both sides and gets stuck:
    eval (uncast_nat (cast_dyn (plus e1 e2)))
    = eval (uncast_nat (cast_dyn (eval_nat(plus e1 e2))))
    = ... (cannot fold to eval (plus e1 e2) without lemma)

  With the lemma, the SC folds directly.
*)

Definition Σ_gradual : Typing.Typing.env :=
  [Examples.Nat_sig; ListNat.List_sig; ListNat.Maybe_sig;
   ListNat.Expr_sig_val; ListNat.Value_sig].
(* I=0:Nat, I=1:List, I=2:Maybe, I=4:Expr, I=5:Value *)

(* ------------------------------------------------------------------ *)
(** Lemma: cast_dyn preserves the underlying value                      *)
(**   eval (cast_dyn e) = v_dyn(v_nat (eval_nat e))                   *)
(**   where eval_nat extracts: eval_nat(const n) = n,                  *)
(**   eval_nat(plus e1 e2) = plus(eval_nat e1)(eval_nat e2)           *)
(* ------------------------------------------------------------------ *)

Definition Γ_e : Typing.Typing.ctx := [ListNat.expr_g_ty].

(** The lemma for the omega rule.
    LHS: gradual_eval (uncast_nat (cast_dyn e))
    RHS: gradual_eval e
    Context: e = tVar 0 *)
Definition lemma_cast_roundtrip : LemmaEnv.lemma := {|
  LemmaEnv.lemma_lhs :=
    tApp ListNat.gradual_eval
         (ListNat.g_uncast_nat (ListNat.g_cast_dyn (tVar 0)));
  LemmaEnv.lemma_rhs :=
    tApp ListNat.gradual_eval (tVar 0)
|}.

(** Validate the lemma by sub-SC *)
Lemma cast_roundtrip_validated :
  LemmaEnv.validate_lemma 160 400 Σ_gradual
    (LemmaEnv.lemma_lhs lemma_cast_roundtrip)
    (LemmaEnv.lemma_rhs lemma_cast_roundtrip)
    ListNat.value_ty = true.
Proof. vm_compute. reflexivity. Qed.

(** Prove a specific instance for grounding:
    cast_dyn (const 2) produces v_dyn(v_nat 2) *)
Definition t_cast_const : tm :=
  tApp ListNat.gradual_eval
       (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ (Examples.succ Examples.zero)))).

Lemma cast_const_ok :
  Supercompile.residualise_jTy 40 100 Σ_gradual
    [ListNat.expr_g_ty] t_cast_const ListNat.value_ty
  = Some (ListNat.v_dyn (ListNat.v_nat (Examples.succ (Examples.succ Examples.zero)))).
Proof. vm_compute. reflexivity. Qed.

(** The unsafe case: uncast on a non-wrapped value produces Wrong *)
Definition t_uncast_safe : tm :=
  tApp ListNat.gradual_eval
       (ListNat.g_uncast_nat (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ Examples.zero)))).

Definition t_uncast_unsafe : tm :=
  tApp ListNat.gradual_eval
       (ListNat.g_uncast_nat (ListNat.g_const (Examples.succ Examples.zero))).

Lemma uncast_safe_ok :
  Supercompile.residualise_jTy 40 100 Σ_gradual
    [ListNat.expr_g_ty] t_uncast_safe ListNat.value_ty
  = Some (ListNat.v_nat (Examples.succ Examples.zero)).
Proof. vm_compute. reflexivity. Qed.

Lemma uncast_unsafe_wrong :
  Supercompile.residualise_jTy 40 100 Σ_gradual
    [ListNat.expr_g_ty] t_uncast_unsafe ListNat.value_ty
  = Some ListNat.v_wrong.
Proof. vm_compute. reflexivity. Qed.

(** The omega-rule lemma proves the main roundtrip property.
    Now test with the lemma-driven SC. *)

Definition r_cast_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ_gradual
    [lemma_cast_roundtrip] Γ_e
    (tApp ListNat.gradual_eval
         (ListNat.g_uncast_nat (ListNat.g_cast_dyn (tVar 0))))
    ListNat.value_ty.

Definition r_id_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ_gradual
    [lemma_cast_roundtrip] Γ_e
    (tApp ListNat.gradual_eval (tVar 0))
    ListNat.value_ty.

Lemma cast_roundtrip_omega :
  r_cast_omega = r_id_omega.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Summary                                                          *)
(**                                                                   *)
(**   cast_const_ok           : cast_dyn(const 2) = v_dyn(v_nat 2)   *)
(**   uncast_safe_ok          : uncast(cast_dyn(const 1)) = v_nat 1  *)
(**   uncast_unsafe_wrong     : uncast(const 1) = Wrong               *)
(**   cast_roundtrip_validated: sub-SC proves omega lemma             *)
(**   cast_roundtrip_omega    : lemma-driven SC fuses both sides      *)
(**                                                                   *)
(**   The SC discovers at COMPILE TIME which casts are safe (produce  *)
(**   v_nat) vs unsafe (produce Wrong) — the key gradual typing       *)
(**   property that blame tracking would attribute to the typed side. *)
(* ------------------------------------------------------------------ *)
