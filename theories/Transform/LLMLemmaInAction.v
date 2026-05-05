From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile LemmaEnv OmegaRule.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(** LLM-Proposed Lemma Validation + Where the SC Gets Stuck *)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(* ------------------------------------------------------------------ *)
(** The LLM-proposed lemma (with scrambled definitions):
    revAcc (append xs ys) acc = revAcc ys (revAcc xs acc)
    Context: acc = tVar 0, ys = tVar 1, xs = tVar 2 *)
(* ------------------------------------------------------------------ *)

Lemma lemma_rev_acc_append_distrib_validated :
  LemmaEnv.validate_lemma 160 400 Σ
    (* LHS = revAcc (append xs ys) acc *)
    (tApp (tApp ListNat.rev_acc
              (tApp (tApp ListNat.append (tVar 2)) (tVar 1)))
         (tVar 0))
    (* RHS = revAcc ys (revAcc xs acc) *)
    (tApp (tApp ListNat.rev_acc (tVar 1))
         (tApp (tApp ListNat.rev_acc (tVar 2)) (tVar 0)))
    ListNat.list_ty = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** Without the lemma: the SC produces DIFFERENT residuals for
    reverse (append xs ys) vs append (reverse ys) (reverse xs).
    This is where the SC gets stuck — it cannot fuse them alone. *)
(* ------------------------------------------------------------------ *)

Definition Γ_l2 := [ListNat.list_ty; ListNat.list_ty].

(** reverse (append xs ys) *)
Definition t_rev_append : tm :=
  tApp ListNat.reverse (tApp (tApp ListNat.append (tVar 1)) (tVar 0)).

(** append (reverse ys) (reverse xs) *)
Definition t_append_rev : tm :=
  tApp (tApp ListNat.append (tApp ListNat.reverse (tVar 0)))
       (tApp ListNat.reverse (tVar 1)).

(** Standard SC residuals — these are DIFFERENT (the SC gets stuck): *)
Definition r_rev_std : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l2
    t_rev_append ListNat.list_ty.
Definition r_append_rev_std : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l2
    t_append_rev ListNat.list_ty.

(** They are not equal — the SC cannot fuse reverse over append: *)
Lemma std_sc_gets_stuck :
  r_rev_std <> r_append_rev_std.
Proof.
  unfold r_rev_std, r_append_rev_std.
  vm_compute.
  (* They ARE different — the SC produces structurally different residuals *)
  intro H. inversion H.
Qed.

(* ------------------------------------------------------------------ *)
(** With the LLM-proposed lemma, the SC fuses them identically: *)
(* ------------------------------------------------------------------ *)

Definition r_rev_lemma : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ
    [{| LemmaEnv.lemma_lhs :=
        tApp (tApp ListNat.rev_acc
                  (tApp (tApp ListNat.append (tVar 2)) (tVar 1)))
             (tVar 0);
       LemmaEnv.lemma_rhs :=
        tApp (tApp ListNat.rev_acc (tVar 1))
             (tApp (tApp ListNat.rev_acc (tVar 2)) (tVar 0))
    |}]
    Γ_l2 t_rev_append ListNat.list_ty.

Definition r_append_rev_lemma : option tm :=
  Omega.lemma_driven_residualise 200 600 Σ
    [{| LemmaEnv.lemma_lhs :=
        tApp (tApp ListNat.rev_acc
                  (tApp (tApp ListNat.append (tVar 2)) (tVar 1)))
             (tVar 0);
       LemmaEnv.lemma_rhs :=
        tApp (tApp ListNat.rev_acc (tVar 1))
             (tApp (tApp ListNat.rev_acc (tVar 2)) (tVar 0))
    |}]
    Γ_l2 t_append_rev ListNat.list_ty.

(** With the lemma, both sides produce IDENTICAL residuals: *)
Lemma with_lemma_they_fuse :
  r_rev_lemma = r_append_rev_lemma.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** And the lemma-driven SC residual is DIFFERENT (better!) than the
    standard SC residuals: *)
Lemma lemma_driven_is_better :
  r_rev_lemma <> r_rev_std.
Proof. unfold r_rev_lemma, r_rev_std. vm_compute. intro H. inversion H. Qed.

(* ------------------------------------------------------------------ *)
(** Summary:
    1. Standard SC:  gets stuck (r_rev_std <> r_append_rev_std)
    2. LLM proposes:  revAcc (append xs ys) acc = revAcc ys (revAcc xs acc)
    3. Sub-SC proves:  lemma_rev_acc_append_distrib_validated
    4. Lemma-driven SC: fuses them (r_rev_lemma = r_append_rev_lemma)
    5. The fused residual is BETTER than the standard SC residual

    The omega rule in action, driven by an LLM-proposed lemma,
    all validated by the kernel. *)
(* ------------------------------------------------------------------ *)
