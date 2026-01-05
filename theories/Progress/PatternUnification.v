From Stdlib Require Import List Bool Arith Utf8 FunctionalExtensionality Lia.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.

(**
  Pattern(-style) anti-unification for dependent judgements.

  Goal: a *computational* procedure that, given two judgements, returns
  - a generalisation judgement (in an extended context of typed holes)
  - substitutions instantiating the generalisation back to each input

  We start with a deliberately conservative fragment:
  - contexts must match syntactically
  - (for typing judgements) result types must match syntactically
  - if the terms differ, we generalise the entire term by a single fresh hole

  This is already useful as a termination-control primitive:
  it yields a concrete substitution witness suitable for creating a back-link.

  Follow-ups (planned):
  - refine generalisation structurally, introducing multiple holes
  - support `jEq` once the judgement language stabilises
  - prove/compute typedness of the returned substitutions using `has_subst`
*)

Section TermEquality.
  Fixpoint list_eqb {A : Type} (eqbA : A -> A -> bool) (xs ys : list A) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs, y :: ys => eqbA x y && list_eqb eqbA xs ys
    | _, _ => false
    end.

  Fixpoint tm_eqb (t u : T.tm) : bool :=
    match t, u with
    | T.tVar x, T.tVar y => Nat.eqb x y
    | T.tSort i, T.tSort j => Nat.eqb i j
    | T.tPi A B, T.tPi A' B' => tm_eqb A A' && tm_eqb B B'
    | T.tLam A t, T.tLam A' t' => tm_eqb A A' && tm_eqb t t'
    | T.tApp t1 u1, T.tApp t2 u2 => tm_eqb t1 t2 && tm_eqb u1 u2
    | T.tFix A t, T.tFix A' t' => tm_eqb A A' && tm_eqb t t'
    | T.tInd ind, T.tInd ind' => Nat.eqb ind ind'
    | T.tRoll ind c ps rs, T.tRoll ind' c' ps' rs' =>
        Nat.eqb ind ind' && Nat.eqb c c'
        && list_eqb tm_eqb ps ps'
        && list_eqb tm_eqb rs rs'
    | T.tCase ind s C0 brs, T.tCase ind' s' C0' brs' =>
        Nat.eqb ind ind'
        && tm_eqb s s'
        && tm_eqb C0 C0'
        && list_eqb tm_eqb brs brs'
    | _, _ => false
    end.

  Fixpoint list_eq_dec {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
      (xs ys : list A) : {xs = ys} + {xs <> ys}.
  Proof.
    decide equality.
  Defined.

  Fixpoint tm_eq_dec (t u : T.tm) : {t = u} + {t <> u}.
  Proof.
    decide equality;
      try apply Nat.eq_dec;
      try apply (list_eq_dec tm_eq_dec).
  Defined.
End TermEquality.

Section PatternAU.
  (* A generalisation result for a term-in-context.
     Holes are represented as fresh variables in a prefix context `holes`.

     If `holes = [H0; H1; ...]`, then the generalised term may contain
     `tVar 0` for the first hole, `tVar 1` for the second, etc.

     Instantiation back to a concrete term uses `Ty.subst_list`.
  *)
  Record au_tm_result : Type := {
    au_holes : list T.tm;
    au_gen : T.tm;
    au_sub1 : list T.tm;
    au_sub2 : list T.tm;
  }.

  Definition au_tm_result_ok (t1 t2 : T.tm) (r : au_tm_result) : Prop :=
    length (au_holes r) = length (au_sub1 r)
    /\ length (au_holes r) = length (au_sub2 r)
    /\ Ty.subst_list (au_sub1 r) (au_gen r) = t1
    /\ Ty.subst_list (au_sub2 r) (au_gen r) = t2.

  Lemma subst_list_nil (t : T.tm) : Ty.subst_list [] t = t.
  Proof.
    unfold Ty.subst_list, Ty.subst_sub.
    assert (Hfun : Ty.sub_fun (0, []) = @Autosubst_Classes.ids T.tm T.Ids_tm).
    { apply functional_extensionality; intro x.
      unfold Ty.sub_fun.
      rewrite nth_error_nil.
      cbn.
      f_equal.
      rewrite Nat.sub_0_r, Nat.add_0_r.
      reflexivity. }
    rewrite Hfun.
    exact (subst_id (SubstLemmas := T.SubstLemmas_tm) t).
  Qed.

  (* Conservative anti-unification at a known type A.
     - if the terms are equal, return them unchanged
     - otherwise, abstract the whole term by a single hole of type A
  *)
  Definition anti_unify_tm_at (A t1 t2 : T.tm) : au_tm_result :=
    match tm_eq_dec t1 t2 with
    | left _ =>
        {| au_holes := [];
           au_gen := t1;
           au_sub1 := [];
           au_sub2 := [] |}
    | right _ =>
        {| au_holes := [A];
           au_gen := T.tVar 0;
           au_sub1 := [t1];
           au_sub2 := [t2] |}
    end.

  Lemma anti_unify_tm_at_ok (A t1 t2 : T.tm) :
    au_tm_result_ok t1 t2 (anti_unify_tm_at A t1 t2).
  Proof.
    unfold anti_unify_tm_at, au_tm_result_ok.
    destruct (tm_eq_dec t1 t2) as [->|Hneq]; simpl.
    - repeat split; try reflexivity.
      + apply subst_list_nil.
      + apply subst_list_nil.
    - repeat split; reflexivity.
  Qed.

  (* Judgement-level anti-unification.

     For now we support the currently-stable judgement constructors
     (`jTy` and `jSub`).

     For `jTy`, we require the contexts and types to match syntactically.
     Then we anti-unify the term at that type.
  *)

  Record au_judgement_result : Type := {
    auJ_holes : list T.tm;
    auJ_gen : C.judgement;
    auJ_sub1 : list T.tm;
    auJ_sub2 : list T.tm;
  }.

  Definition au_jTy (Γ : Ty.ctx) (t1 t2 A : T.tm) : au_judgement_result :=
    let r := anti_unify_tm_at A t1 t2 in
    {| auJ_holes := au_holes r;
       auJ_gen := C.jTy (au_holes r ++ Γ) (au_gen r) A;
       auJ_sub1 := au_sub1 r;
       auJ_sub2 := au_sub2 r |}.

  (* NOTE: The current `Typing.Cyclic.judgement` in this repo does not expose `jEq`.
     Once it does, we will add an `au_jEq` case that anti-unifies all components. *)

  Definition anti_unify_judgement (j1 j2 : C.judgement) : option au_judgement_result :=
    match j1, j2 with
    | C.jTy Γ t A, C.jTy Γ' t' A' =>
        if list_eqb tm_eqb Γ Γ' && tm_eqb A A' then
          Some (au_jTy Γ t t' A)
        else None
    | C.jSub Δ s Γ, C.jSub Δ' s' Γ' =>
        (* for now: only succeed on syntactic equality *)
        if list_eqb tm_eqb Δ Δ' && list_eqb tm_eqb Γ Γ'
           && Nat.eqb (Ty.sub_k s) (Ty.sub_k s')
           && list_eqb tm_eqb (Ty.sub_list s) (Ty.sub_list s')
        then
          Some {| auJ_holes := [];
                  auJ_gen := j1;
                  auJ_sub1 := [];
                  auJ_sub2 := [] |}
        else None
    | _, _ => None
    end.

  (* A minimal correctness statement for the `jTy` case:
     the returned term-level substitutions reconstruct the input terms.

     (Typing of these substitutions is a later theorem once we connect
      `auJ_holes` to a typed hole context and prove `has_subst`.)
  *)
  Lemma anti_unify_jTy_reconstruct (Γ : Ty.ctx) (t1 t2 A : T.tm) :
    let rJ := au_jTy Γ t1 t2 A in
    let rT := anti_unify_tm_at A t1 t2 in
    auJ_holes rJ = au_holes rT
    /\ auJ_sub1 rJ = au_sub1 rT
    /\ auJ_sub2 rJ = au_sub2 rT
    /\ Ty.subst_list (auJ_sub1 rJ) (au_gen rT) = t1
    /\ Ty.subst_list (auJ_sub2 rJ) (au_gen rT) = t2.
  Proof.
    intros rJ rT.
    repeat split; try reflexivity.
    all: destruct (anti_unify_tm_at_ok A t1 t2) as [_ [_ [H1 H2]]]; assumption.
  Qed.
End PatternAU.
