From Stdlib Require Import List Arith Utf8.

From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.

Section HomeomorphicEmbedding.
  (*
     Homeomorphic embedding (HE) is a classic termination control tool for
     partial evaluation / supercompilation. Here we extend it to our *typed
     judgements* so it can be used as an unfold-control / back-link criterion
     during cyclic proof normalization.

     This file intentionally starts lightweight:
     - definitions for terms, lists, and CIC-style judgements
     - basic reflexivity lemmas

     Stronger results (transitivity, wqo, interaction with typing/equality)
     are planned follow-ups.
  *)

  Inductive emb_list {A : Type} (embA : A -> A -> Prop) : list A -> list A -> Prop :=
  | emb_list_nil : emb_list embA [] []
  | emb_list_cons x xs y ys :
      embA x y ->
      emb_list embA xs ys ->
      emb_list embA (x :: xs) (y :: ys)
  | emb_list_skip x xs ys :
      emb_list embA xs ys ->
      emb_list embA (x :: xs) ys.

  Inductive emb_tm : T.tm -> T.tm -> Prop :=
  | emb_refl t : emb_tm t t

  (* Diving: the larger term contains an embedding somewhere inside. *)
  | emb_dive_piA A B u : emb_tm A u -> emb_tm (T.tPi A B) u
  | emb_dive_piB A B u : emb_tm B u -> emb_tm (T.tPi A B) u
  | emb_dive_lamA A t u : emb_tm A u -> emb_tm (T.tLam A t) u
  | emb_dive_lamt A t u : emb_tm t u -> emb_tm (T.tLam A t) u
  | emb_dive_app1 t u v : emb_tm t v -> emb_tm (T.tApp t u) v
  | emb_dive_app2 t u v : emb_tm u v -> emb_tm (T.tApp t u) v
  | emb_dive_fixA A t u : emb_tm A u -> emb_tm (T.tFix A t) u
  | emb_dive_fixt A t u : emb_tm t u -> emb_tm (T.tFix A t) u
  | emb_dive_roll_arg I c args u :
      In u args -> emb_tm (T.tRoll I c args) u
  | emb_dive_case_scrut I scrut C brs u : emb_tm scrut u -> emb_tm (T.tCase I scrut C brs) u
  | emb_dive_case_C I scrut C brs u : emb_tm C u -> emb_tm (T.tCase I scrut C brs) u
  | emb_dive_case_branch I scrut C brs u :
      In u brs -> emb_tm (T.tCase I scrut C brs) u

  (* Coupling: same head constructor, recursively embed arguments. *)
  | emb_sort i : emb_tm (T.tSort i) (T.tSort i)
  | emb_var x : emb_tm (T.tVar x) (T.tVar x)
  | emb_ind I args args' :
      emb_list emb_tm args args' ->
      emb_tm (T.tInd I args) (T.tInd I args')

  | emb_pi A A' B B' :
      emb_tm A A' ->
      emb_tm B B' ->
      emb_tm (T.tPi A B) (T.tPi A' B')

  | emb_lam A A' t t' :
      emb_tm A A' ->
      emb_tm t t' ->
      emb_tm (T.tLam A t) (T.tLam A' t')

  | emb_app t t' u u' :
      emb_tm t t' ->
      emb_tm u u' ->
      emb_tm (T.tApp t u) (T.tApp t' u')

  | emb_fix A A' t t' :
      emb_tm A A' ->
      emb_tm t t' ->
      emb_tm (T.tFix A t) (T.tFix A' t')

  | emb_roll I c args args' :
      emb_list emb_tm args args' ->
      emb_tm (T.tRoll I c args) (T.tRoll I c args')

  | emb_case I scrut scrut' C0 C0' brs brs' :
      emb_tm scrut scrut' ->
      emb_tm C0 C0' ->
      emb_list emb_tm brs brs' ->
      emb_tm (T.tCase I scrut C0 brs) (T.tCase I scrut' C0' brs').

  Definition emb_ctx : Ty.ctx -> Ty.ctx -> Prop :=
    emb_list emb_tm.

  Definition emb_sub (s1 s2 : Ty.sub) : Prop :=
    Ty.sub_k s1 = Ty.sub_k s2 /\
    emb_list emb_tm (Ty.sub_list s1) (Ty.sub_list s2).

  Inductive emb_judgement : C.judgement -> C.judgement -> Prop :=
  | emb_jTy Γ Δ t u A B :
      emb_ctx Γ Δ -> emb_tm t u -> emb_tm A B ->
      emb_judgement (C.jTy Γ t A) (C.jTy Δ u B)
  | emb_jEq Γ Δ t t' u u' A B :
      emb_ctx Γ Δ -> emb_tm t t' -> emb_tm u u' -> emb_tm A B ->
      emb_judgement (C.jEq Γ t u A) (C.jEq Δ t' u' B)
  | emb_jSub Δ Δ' s s' Γ Γ' :
      emb_ctx Δ Δ' -> emb_sub s s' -> emb_ctx Γ Γ' ->
      emb_judgement (C.jSub Δ s Γ) (C.jSub Δ' s' Γ').

  Lemma emb_list_refl {A : Type} (embA : A -> A -> Prop) :
    (forall x, embA x x) -> forall xs, emb_list embA xs xs.
  Proof.
    intros Hrefl xs.
    induction xs as [|x xs IH].
    - constructor.
    - econstructor; eauto.
  Qed.

  Lemma emb_tm_refl (t : T.tm) : emb_tm t t.
  Proof.
    apply emb_refl.
  Qed.

  Lemma emb_ctx_refl (Γ : Ty.ctx) : emb_ctx Γ Γ.
  Proof.
    unfold emb_ctx.
    apply (emb_list_refl emb_tm).
    intro t. exact (emb_tm_refl t).
  Qed.

  Lemma emb_sub_refl (s : Ty.sub) : emb_sub s s.
  Proof.
    unfold emb_sub.
    split; [reflexivity|].
    apply (emb_list_refl emb_tm).
    intro t. exact (emb_tm_refl t).
  Qed.

  Lemma emb_judgement_refl (j : C.judgement) : emb_judgement j j.
  Proof.
    destruct j as [Γ t A|Γ t u A|Δ s Γ].
    - apply emb_jTy; [apply emb_ctx_refl|apply emb_tm_refl|apply emb_tm_refl].
    - apply emb_jEq; [apply emb_ctx_refl|apply emb_tm_refl|apply emb_tm_refl|apply emb_tm_refl].
    - apply emb_jSub; [apply emb_ctx_refl|apply emb_sub_refl|apply emb_ctx_refl].
  Qed.
End HomeomorphicEmbedding.
