From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile LemmaEnv OmegaRule.
Import Term.Syntax. Import ListNotations.
Set Default Proof Using "Type".

(** Plus Commutativity via Omega Rule

    Theorem: plusL m n = plusL n m

    Two unconditional lemmas, each proved by sub-SC:
    Lemma A: plusL m 0 = m       (right identity)
    Lemma B: plusL m (succ n) = succ (plusL m n)  (succ commutes)

    The standard proof:
    - Induction on m
    - Base: plusL 0 n = n, RHS = plusL n 0 → Lemma A: plusL n 0 = n ✓
    - Step: plusL (succ m') n = succ(plusL m' n)
            RHS: plusL n (succ m') → Lemma B: succ(plusL n m')
            By IH: plusL m' n = plusL n m' → both equal ✓
*)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(** Lemma A: plusL m 0 = m
    m = tVar 0.  Both sides SC to the same residual after Lemma B is applied. *)
Definition lemma_plus_right_id : LemmaEnv.lemma := {|
  LemmaEnv.lemma_lhs := tApp (tApp Examples.plusL (tVar 0)) Examples.zero;
  LemmaEnv.lemma_rhs := tVar 0
|}.

(** Lemma B: plusL m (succ n) = succ (plusL m n)
    m = tVar 1, n = tVar 0 *)
Definition lemma_plus_succ : LemmaEnv.lemma := {|
  LemmaEnv.lemma_lhs :=
    tApp (tApp Examples.plusL (tVar 1)) (Examples.succ (tVar 0));
  LemmaEnv.lemma_rhs :=
    Examples.succ (tApp (tApp Examples.plusL (tVar 1)) (tVar 0))
|}.

(** Commutativity: plusL m n = plusL n m
    Context: n = tVar 0, m = tVar 1 *)
Definition Γ_mn : Typing.Typing.ctx := [Examples.nat_ty; Examples.nat_ty].

Definition t_plus_comm_lhs : tm :=
  tApp (tApp Examples.plusL (tVar 1)) (tVar 0).

Definition t_plus_comm_rhs : tm :=
  tApp (tApp Examples.plusL (tVar 0)) (tVar 1).

(** Standard SC (no lemmas): does it fuse?
    Expected: NO — the two sides produce different residuals *)
Definition r_comm_lhs_std : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_mn
    t_plus_comm_lhs Examples.nat_ty.
Definition r_comm_rhs_std : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_mn
    t_plus_comm_rhs Examples.nat_ty.

Lemma std_sc_cannot_prove_comm :
  r_comm_lhs_std <> r_comm_rhs_std.
Proof. unfold r_comm_lhs_std, r_comm_rhs_std. vm_compute.
  intro H. inversion H. Qed.

(** With both lemmas: *)
Definition r_comm_lhs_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ
    [lemma_plus_right_id; lemma_plus_succ]
    Γ_mn t_plus_comm_lhs Examples.nat_ty.

Definition r_comm_rhs_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ
    [lemma_plus_right_id; lemma_plus_succ]
    Γ_mn t_plus_comm_rhs Examples.nat_ty.

(** The omega rule fuses commutativity: *)
Theorem plus_commutativity :
  r_comm_lhs_omega = r_comm_rhs_omega.
Proof. vm_compute. reflexivity. Qed.

(** And the fused residual differs from the standalone residuals: *)
Lemma omega_better_than_std :
  r_comm_lhs_omega <> r_comm_lhs_std.
Proof. unfold r_comm_lhs_omega, r_comm_lhs_std.
  vm_compute. intro H. inversion H. Qed.
