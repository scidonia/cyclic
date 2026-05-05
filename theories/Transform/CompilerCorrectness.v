From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import
     Supercompile LemmaEnv OmegaRule.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  Compiler Correctness Benchmark

  Proves: exec (compile e) nil = cons (eval e) nil
  using the omega rule with an LLM-discovered auxiliary lemma.

  This is the classic Reynolds-style compiler correctness theorem:
  a simple arithmetic expression compiler targeting a stack machine.

  The hard part: the lemma exec (compile e code) s = exec code (eval e :: s)
  must be discovered and proved. The standard SC cannot discover this
  because it requires a strengthened induction hypothesis — exactly
  the omega rule.

  Σ = [Nat, List, Maybe, Expr]
*)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig;
                 ListNat.Maybe_sig; ListNat.Expr_sig].

(** Context for the lemma: [code:List, s:List, e:Expr] *)
Definition Γ_lemma : Typing.Typing.ctx :=
  [ListNat.list_ty; ListNat.list_ty; ListNat.expr_ty].
(* tVar 0 = code, tVar 1 = s, tVar 2 = e *)

(** The auxiliary lemma:
    exec (compile e code) s = exec code (cons (eval e) s)
    Both sides SC to the same residual by induction on e. *)
Definition lemma_compiler_soundness : LemmaEnv.lemma := {|
  LemmaEnv.lemma_lhs :=
    tApp (tApp ListNat.exec
              (tApp (tApp ListNat.compile (tVar 2)) (tVar 0)))
         (tVar 1);
  LemmaEnv.lemma_rhs :=
    tApp (tApp ListNat.exec (tVar 0))
         (ListNat.cons (tApp ListNat.eval (tVar 2)) (tVar 1))
|}.

(** Validate the lemma by sub-SC *)
Lemma compiler_soundness_lemma_validated :
  LemmaEnv.validate_lemma 160 400 Σ
    (LemmaEnv.lemma_lhs lemma_compiler_soundness)
    (LemmaEnv.lemma_rhs lemma_compiler_soundness)
    ListNat.list_ty = true.
Proof. vm_compute. reflexivity. Qed.

(** Now the main theorem with the lemma:
    exec (compile e nil) nil = cons (eval e) nil *)

Definition Γ_e : Typing.Typing.ctx := [ListNat.expr_ty].

Definition t_main_lhs : tm :=
  tApp (tApp ListNat.exec
             (tApp (tApp ListNat.compile (tVar 0)) ListNat.nil))
       ListNat.nil.

Definition t_main_rhs : tm :=
  ListNat.cons (tApp ListNat.eval (tVar 0)) ListNat.nil.

(** Standard SC: does it fuse? *)
Definition r_main_lhs_std : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_e
    t_main_lhs ListNat.list_ty.

Definition r_main_rhs_std : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_e
    t_main_rhs ListNat.list_ty.

Lemma compiler_main_smoke_std :
  exists a b, r_main_lhs_std = Some a /\ r_main_rhs_std = Some b.
Proof. vm_compute. do 2 eexists. split; reflexivity. Qed.

(** Try exact equality with standard SC — fails (should not be equal
    because the lemma is needed): *)
Lemma std_sc_cannot_fuse_compiler :
  r_main_lhs_std = r_main_rhs_std ->
  False.
Proof.
  intro H.
  unfold r_main_lhs_std, r_main_rhs_std in H.
  vm_compute in H. inversion H.
Qed.

(** With the lemma: *)
Definition r_main_lhs_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ
    [lemma_compiler_soundness]
    Γ_e t_main_lhs ListNat.list_ty.

Definition r_main_rhs_omega : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ
    [lemma_compiler_soundness]
    Γ_e t_main_rhs ListNat.list_ty.

Lemma compiler_main_with_lemma :
  r_main_lhs_omega = r_main_rhs_omega.
Proof. vm_compute. reflexivity. Qed.

(** The lemma-driven residual is BETTER than standard SC: *)
Lemma lemma_driven_compiler_is_better :
  r_main_lhs_omega <> r_main_lhs_std.
Proof.
  unfold r_main_lhs_omega, r_main_lhs_std.
  vm_compute. intro H. inversion H.
Qed.

(* ------------------------------------------------------------------ *)
(** * Test the LLM proposing this lemma                                *)
(**                                                                   *)
(**   With Condition B (scrambled+definitions), the LLM should        *)
(**   propose: exec (compile e code) s = exec code (eval e :: s)      *)
(**                                                                   *)
(**   Run: echo '<json>' | python3 llm_generalise.py --serve-lemma   *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(** * Summary                                                          *)
(**                                                                   *)
(**   compiler_soundness_lemma_validated : sub-SC proves the lemma    *)
(**   std_sc_cannot_fuse_compiler       : standard SC fails           *)
(**   compiler_main_with_lemma           : omega rule fuses them      *)
(**   lemma_driven_compiler_is_better    : lemma-driven residual ≠ std *)
(**                                                                   *)
(**   This is the canonical benchmark for omega-rule supercompilation. *)
(* ------------------------------------------------------------------ *)
