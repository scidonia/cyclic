From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(** Canonical Gradual Typing Examples — SC Reducibility

    Tests whether the SC reduces common cast patterns from the
    gradual typing literature. All are concrete expressions;
    the omega-rule version (symbolic e) is in GradualCast.v.

    Σ = [Nat, List, Maybe, Expr_gradual, Value]
*)

Definition Σ_gradual : Typing.Typing.env :=
  [Examples.Nat_sig; ListNat.List_sig; ListNat.Maybe_sig;
   ListNat.Expr_sig_val; ListNat.Value_sig].

(* ------------------------------------------------------------------ *)
(** Example 1: Safe cast roundtrip — the classic scott-encoding test *)
(* ------------------------------------------------------------------ *)

Definition e1 : tm :=
  ListNat.g_uncast_nat (ListNat.g_cast_dyn
    (ListNat.g_const (Examples.succ (Examples.succ Examples.zero)))).

Lemma safe_cast_const : forall fuel,
  Supercompile.residualise_jTy fuel fuel Σ_gradual
    [ListNat.expr_g_ty] (tApp ListNat.gradual_eval e1) ListNat.value_ty
  = Some (ListNat.v_nat (Examples.succ (Examples.succ Examples.zero))).
Proof. intro fuel. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** Example 2: Unsafe cast — uncast on a non-wrapped nat              *)
(* ------------------------------------------------------------------ *)

Definition e2 : tm :=
  ListNat.g_uncast_nat (ListNat.g_const
    (Examples.succ (Examples.succ Examples.zero))).

Lemma unsafe_cast_wrong : forall fuel,
  Supercompile.residualise_jTy fuel fuel Σ_gradual
    [ListNat.expr_g_ty] (tApp ListNat.gradual_eval e2) ListNat.value_ty
  = Some ListNat.v_wrong.
Proof. intro fuel. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** Example 3: Nested safe — cast pair through addition               *)
(* ------------------------------------------------------------------ *)

Definition e3 : tm :=
  ListNat.g_uncast_nat (ListNat.g_plus
    (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ Examples.zero)))
    (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ (Examples.succ Examples.zero))))).

Lemma nested_safe : forall fuel,
  Supercompile.residualise_jTy fuel fuel Σ_gradual
    [ListNat.expr_g_ty] (tApp ListNat.gradual_eval e3) ListNat.value_ty
  = Some (ListNat.v_nat (Examples.succ (Examples.succ (Examples.succ Examples.zero)))).
Proof. intro fuel. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** Example 4: Mixed safe/unsafe — one operand is wrong               *)
(* ------------------------------------------------------------------ *)

Definition e4 : tm :=
  ListNat.g_uncast_nat (ListNat.g_plus
    (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ Examples.zero)))
    (ListNat.g_const (Examples.succ (Examples.succ Examples.zero)))).

Lemma mixed_blame : forall fuel,
  Supercompile.residualise_jTy fuel fuel Σ_gradual
    [ListNat.expr_g_ty] (tApp ListNat.gradual_eval e4) ListNat.value_ty
  = Some ListNat.v_wrong.
Proof. intro fuel. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** Example 5: Double roundtrip — cast_dyn(uncast_nat(cast_dyn(...))) *)
(* ------------------------------------------------------------------ *)

Definition e5 : tm :=
  ListNat.g_uncast_nat (ListNat.g_cast_dyn
    (ListNat.g_uncast_nat (ListNat.g_cast_dyn
      (ListNat.g_const (Examples.succ (Examples.succ (Examples.succ Examples.zero))))))).

Lemma double_roundtrip : forall fuel,
  Supercompile.residualise_jTy fuel fuel Σ_gradual
    [ListNat.expr_g_ty] (tApp ListNat.gradual_eval e5) ListNat.value_ty
  = Some (ListNat.v_nat (Examples.succ (Examples.succ (Examples.succ Examples.zero)))).
Proof. intro fuel. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** Example 6: Cast_dyn inside plus, uncast outside — proxy pattern   *)
(* ------------------------------------------------------------------ *)

Definition e6 : tm :=
  ListNat.g_uncast_nat
    (ListNat.g_plus
      (ListNat.g_plus
        (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ Examples.zero)))
        (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ Examples.zero))))
      (ListNat.g_cast_dyn (ListNat.g_const (Examples.succ Examples.zero)))).

Lemma proxy_pattern : forall fuel,
  Supercompile.residualise_jTy fuel fuel Σ_gradual
    [ListNat.expr_g_ty] (tApp ListNat.gradual_eval e6) ListNat.value_ty
  = Some (ListNat.v_nat (Examples.succ (Examples.succ (Examples.succ Examples.zero)))).
Proof. intro fuel. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Summary
    The SC reduces ALL canonical gradual typing cast patterns to their
    expected values — concrete safe casts produce v_nat(n), concrete
    unsafe casts produce v_wrong.  The SC acts as a compile-time cast
    checker.

    Test matrix:
    1. safe_cast_const     ✓ cast roundtrip of a constant
    2. unsafe_cast_wrong   ✓ uncast without prior cast → Wrong
    3. nested_safe         ✓ cast through addition
    4. mixed_blame          ✓ partial cast → Wrong (blame)
    5. double_roundtrip    ✓ nested cast pairs
    6. proxy_pattern       ✓ deep cast nesting
*)
