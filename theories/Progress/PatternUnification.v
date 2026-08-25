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
    | T.tInd ind args, T.tInd ind' args' =>
        Nat.eqb ind ind' && list_eqb tm_eqb args args'
    | T.tRoll ind c args, T.tRoll ind' c' args' =>
        Nat.eqb ind ind' && Nat.eqb c c'
        && list_eqb tm_eqb args args'
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

  (** Soundness: if eqb returns true, terms are equal *)
  Lemma list_eqb_eq : forall {A : Type} (eqbA : A -> A -> bool),
    (forall x y, eqbA x y = true -> x = y) ->
    forall xs ys, list_eqb eqbA xs ys = true -> xs = ys.
  Proof.
    intros A eqbA HeqbA.
    induction xs as [|x xs IH]; intros [|y ys] Heq; simpl in Heq; try discriminate.
    - reflexivity.
    - apply andb_true_iff in Heq as [Hxy Hxsys].
      f_equal; auto.
  Qed.

  Lemma tm_eqb_eq : forall t u, tm_eqb t u = true -> t = u.
  Proof.
    fix IH 1.
    intros [x|i|A B|A t|t1 t2|A t|I args|I c args|I s C brs]
           [y|j|A' B'|A' u|u1 u2|A' u|I' args'|I' c' args'|I' s' C' brs'];
      cbn; try discriminate; intro Heq.
    - apply Nat.eqb_eq in Heq. f_equal. exact Heq.
    - apply Nat.eqb_eq in Heq. f_equal. exact Heq.
    - apply andb_true_iff in Heq as [HA HB]. f_equal; [exact (IH A A' HA)|exact (IH B B' HB)].
    - apply andb_true_iff in Heq as [HA Ht]. f_equal; [exact (IH A A' HA)|exact (IH t u Ht)].
    - apply andb_true_iff in Heq as [H1 H2]. f_equal; [exact (IH t1 u1 H1)|exact (IH t2 u2 H2)].
    - apply andb_true_iff in Heq as [HA Ht]. f_equal; [exact (IH A A' HA)|exact (IH t u Ht)].
    - apply andb_true_iff in Heq as [HI Hargs].
      apply Nat.eqb_eq in HI; subst I'. f_equal.
      revert args' Hargs.
      induction args as [|a as' IHas]; intros [|a' as''] Hargs; cbn in Hargs; try discriminate.
      + reflexivity.
      + apply andb_true_iff in Hargs as [Haa' Has'].
        f_equal. exact (IH a a' Haa'). apply IHas. exact Has'.
    - apply andb_true_iff in Heq as [HIc Hargs].
      apply andb_true_iff in HIc as [HI Hc].
      apply Nat.eqb_eq in HI; apply Nat.eqb_eq in Hc; subst I' c'. f_equal.
      revert args' Hargs.
      induction args as [|a as' IHas]; intros [|a' as''] Hargs; cbn in Hargs; try discriminate.
      + reflexivity.
      + apply andb_true_iff in Hargs as [Haa' Has'].
        f_equal. exact (IH a a' Haa'). apply IHas. exact Has'.
    - apply andb_true_iff in Heq as [Hrest Hbrs].
      apply andb_true_iff in Hrest as [Hrest2 HC].
      apply andb_true_iff in Hrest2 as [HI Hs].
      apply Nat.eqb_eq in HI; subst I'. f_equal.
      * exact (IH s s' Hs).
      * exact (IH C C' HC).
      * revert brs' Hbrs.
        induction brs as [|b bs' IHbs]; intros [|b' bs''] Hbrs; cbn in Hbrs; try discriminate.
        -- reflexivity.
        -- apply andb_true_iff in Hbrs as [Hbb' Hbs'].
           f_equal. exact (IH b b' Hbb'). apply IHbs. exact Hbs'.
  Qed.

  (** Completeness: if eqb returns false, terms differ *)
  Lemma list_eqb_neq : forall {A : Type} (eqbA : A -> A -> bool),
    (forall x y, eqbA x y = false -> x <> y) ->
    forall xs ys, list_eqb eqbA xs ys = false -> xs <> ys.
  Proof.
    intros A eqbA HeqbA.
    induction xs as [|x xs IH]; intros [|y ys] Heq; cbn in Heq; try discriminate.
    apply andb_false_iff in Heq as [Hxy|Hxsys].
    - intro H. injection H as Hx _. apply (HeqbA x y Hxy). exact Hx.
    - intro H. injection H as _ Hys. apply (IH ys Hxsys). exact Hys.
  Qed.

  Lemma tm_eqb_refl : forall t, tm_eqb t t = true.
  Proof.
    fix IH 1.
    intro t. destruct t; cbn.
    - apply Nat.eqb_refl.
    - apply Nat.eqb_refl.
    - apply andb_true_iff. split; apply IH.
    - apply andb_true_iff. split; apply IH.
    - apply andb_true_iff. split; apply IH.
    - apply andb_true_iff. split; apply IH.
    - apply andb_true_iff. split; [apply Nat.eqb_refl|].
      induction args as [|a as' IHl]; cbn; [reflexivity|].
      apply andb_true_iff. split; [apply IH|exact IHl].
    - apply andb_true_iff. split.
      + apply andb_true_iff. split; apply Nat.eqb_refl.
      + induction args as [|a as' IHl]; cbn; [reflexivity|].
        apply andb_true_iff. split; [apply IH|exact IHl].
    - apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * apply andb_true_iff. split; [apply Nat.eqb_refl|apply IH].
        * apply IH.
      + induction brs as [|b bs' IHl]; cbn; [reflexivity|].
        apply andb_true_iff. split; [apply IH|exact IHl].
  Qed.

  Lemma tm_eqb_neq : forall t u, tm_eqb t u = false -> t <> u.
  Proof.
    intros t u Hneq Heq.
    subst u. rewrite (tm_eqb_refl t) in Hneq. discriminate.
  Qed.

  (** Reflection: decidable equality via boolean *)
  Lemma tm_eqb_reflect : forall t u, reflect (t = u) (tm_eqb t u).
  Proof.
    intros. destruct (tm_eqb t u) eqn:Heq.
    - constructor. apply tm_eqb_eq. auto.
    - constructor. apply tm_eqb_neq. auto.
  Qed.
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

  (** Structural anti-unification at a known type A.

      This preserves enough structure (apps/cases/constructor arguments) for the
      supercompiler to discover fusion/deforestation.

      The reconstruction proof is still TODO and currently admitted.
  *)

  Definition au_refl (t : T.tm) : au_tm_result :=
    {| au_holes := [];
       au_gen := t;
       au_sub1 := [];
       au_sub2 := [] |}.

  Definition au_hole (A t1 t2 : T.tm) : au_tm_result :=
    {| au_holes := [A];
       au_gen := T.tVar 0;
       au_sub1 := [t1];
       au_sub2 := [t2] |}.

  Definition au_merge2 (r1 r2 : au_tm_result) (mk : T.tm -> T.tm -> T.tm) : au_tm_result :=
    let h1 := au_holes r1 in
    let h2 := au_holes r2 in
    {| au_holes := h1 ++ h2;
       au_gen := mk (au_gen r1) (T.shift (length h1) 0 (au_gen r2));
       au_sub1 := au_sub1 r1 ++ au_sub1 r2;
       au_sub2 := au_sub2 r1 ++ au_sub2 r2 |}.

  Record au_list_result : Type := {
    auL_holes : list T.tm;
    auL_gen : list T.tm;
    auL_sub1 : list T.tm;
    auL_sub2 : list T.tm;
  }.

  Definition auL_nil : au_list_result :=
    {| auL_holes := []; auL_gen := []; auL_sub1 := []; auL_sub2 := [] |}.

  Definition auL_cons (r : au_tm_result) (rtail : au_list_result) : au_list_result :=
    let h := au_holes r in
    {| auL_holes := h ++ auL_holes rtail;
       auL_gen := au_gen r :: map (T.shift (length h) 0) (auL_gen rtail);
       auL_sub1 := au_sub1 r ++ auL_sub1 rtail;
       auL_sub2 := au_sub2 r ++ auL_sub2 rtail |}.

  Fixpoint anti_unify_tm_at (A t1 t2 : T.tm) : au_tm_result :=
    match tm_eq_dec t1 t2 with
    | left _ => au_refl t1
    | right _ =>
        match t1, t2 with
        | T.tApp f1 a1, T.tApp f2 a2 =>
            au_merge2 (anti_unify_tm_at (T.tSort 0) f1 f2) (anti_unify_tm_at A a1 a2) T.tApp
        | T.tLam A1 b1, T.tLam A2 b2 =>
            au_merge2 (anti_unify_tm_at (T.tSort 0) A1 A2) (anti_unify_tm_at A b1 b2) T.tLam
        | T.tPi A1 B1, T.tPi A2 B2 =>
            au_merge2 (anti_unify_tm_at (T.tSort 0) A1 A2) (anti_unify_tm_at (T.tSort 0) B1 B2) T.tPi
        | T.tFix A1 b1, T.tFix A2 b2 =>
            au_merge2 (anti_unify_tm_at (T.tSort 0) A1 A2) (anti_unify_tm_at A b1 b2) T.tFix
        | T.tInd ind args, T.tInd ind' args' =>
            if Nat.eqb ind ind' then
              let fix go xs ys : option au_list_result :=
                match xs, ys with
                | [], [] => Some auL_nil
                | x :: xs, y :: ys =>
                    match go xs ys with
                    | None => None
                    | Some rtail => Some (auL_cons (anti_unify_tm_at (T.tSort 0) x y) rtail)
                    end
                | _, _ => None
                end
              in
              match go args args' with
              | None => au_hole A t1 t2
              | Some rargs =>
                  {| au_holes := auL_holes rargs;
                     au_gen := T.tInd ind (auL_gen rargs);
                     au_sub1 := auL_sub1 rargs;
                     au_sub2 := auL_sub2 rargs |}
              end
            else au_hole A t1 t2
        | T.tRoll ind c args, T.tRoll ind' c' args' =>
            if Nat.eqb ind ind' && Nat.eqb c c' then
              let fix go xs ys : option au_list_result :=
                match xs, ys with
                | [], [] => Some auL_nil
                | x :: xs, y :: ys =>
                    match go xs ys with
                    | None => None
                    | Some rtail => Some (auL_cons (anti_unify_tm_at (T.tSort 0) x y) rtail)
                    end
                | _, _ => None
                end
              in
              match go args args' with
              | None => au_hole A t1 t2
              | Some rargs =>
                  {| au_holes := auL_holes rargs;
                     au_gen := T.tRoll ind c (auL_gen rargs);
                     au_sub1 := auL_sub1 rargs;
                     au_sub2 := auL_sub2 rargs |}
              end
            else au_hole A t1 t2
        | T.tCase ind s1 C1 brs1, T.tCase ind' s2 C2 brs2 =>
            if Nat.eqb ind ind' then
              let fix go xs ys : option au_list_result :=
                match xs, ys with
                | [], [] => Some auL_nil
                | x :: xs, y :: ys =>
                    match go xs ys with
                    | None => None
                    | Some rtail => Some (auL_cons (anti_unify_tm_at (T.tSort 0) x y) rtail)
                    end
                | _, _ => None
                end
              in
              match go brs1 brs2 with
              | None => au_hole A t1 t2
              | Some rbrs =>
                  let rs := anti_unify_tm_at (T.tSort 0) s1 s2 in
                  let rC := anti_unify_tm_at (T.tSort 0) C1 C2 in
                  let hs := au_holes rs in
                  let hC := au_holes rC in
                  let hB := auL_holes rbrs in
                  {| au_holes := hs ++ hC ++ hB;
                     au_gen :=
                       T.tCase ind
                         (au_gen rs)
                         (T.shift (length hs) 0 (au_gen rC))
                         (map (T.shift (length hs + length hC) 0) (auL_gen rbrs));
                     au_sub1 := au_sub1 rs ++ au_sub1 rC ++ auL_sub1 rbrs;
                     au_sub2 := au_sub2 rs ++ au_sub2 rC ++ auL_sub2 rbrs |}
              end
            else au_hole A t1 t2
        | _, _ => au_hole A t1 t2
        end
    end.

  Lemma anti_unify_tm_at_ok (A t1 t2 : T.tm) :
    au_tm_result_ok t1 t2 (anti_unify_tm_at A t1 t2).
  Proof.
  Admitted.

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

  (** Canonicalise a typing judgement by trimming/renaming free variables.

      This is a judgement-level analogue of the canonicalisation done in the
      supercompiler: it makes anti-unification robust under variable renaming and
      context re-ordering that arise from case-splitting.

      We use "first occurrence" order (Jones-style) rather than numeric sorting.
  *)

  Fixpoint nub_nat (xs : list nat) : list nat :=
    match xs with
    | [] => []
    | x :: xs =>
        let ys := nub_nat xs in
        if existsb (Nat.eqb x) ys then ys else x :: ys
    end.

  Fixpoint fv_under_binder (xs : list nat) : list nat :=
    match xs with
    | [] => []
    | x :: xs =>
        match x with
        | 0 => fv_under_binder xs
        | S x => x :: fv_under_binder xs
        end
    end.

  Fixpoint fv_tm (t : T.tm) : list nat :=
    match t with
    | T.tVar x => [x]
    | T.tSort _ => []
    | T.tPi A B => fv_tm A ++ fv_under_binder (fv_tm B)
    | T.tLam A body => fv_tm A ++ fv_under_binder (fv_tm body)
    | T.tApp t1 t2 => fv_tm t1 ++ fv_tm t2
    | T.tFix A body => fv_tm A ++ fv_under_binder (fv_tm body)
    | T.tInd _ args => concat (map fv_tm args)
    | T.tRoll _ _ args => concat (map fv_tm args)
    | T.tCase _ scrut C0 brs => fv_tm scrut ++ fv_under_binder (fv_tm C0) ++ concat (map fv_tm brs)
    end.

  Fixpoint index_of (x : nat) (xs : list nat) : option nat :=
    match xs with
    | [] => None
    | y :: ys => if Nat.eqb x y then Some 0 else option_map S (index_of x ys)
    end.

  Definition canon_jTy (Γ : Ty.ctx) (t A : T.tm) : C.judgement :=
    let keep := nub_nat (fv_tm t ++ fv_tm A) in
    let renfun := fun x => match index_of x keep with | Some i => i | None => 0 end in
    let pick_ty :=
          fun x =>
            match nth_error Γ x with
            | Some B => T.rename renfun B
            | None => T.tVar 0
            end
    in
    let Γ' := map pick_ty keep in
    C.jTy Γ' (T.rename renfun t) (T.rename renfun A).

  Definition canon_judgement (j : C.judgement) : C.judgement :=
    match j with
    | C.jTy Γ t A => canon_jTy Γ t A
    | _ => j
    end.

  Definition anti_unify_judgement (j1 j2 : C.judgement) : option au_judgement_result :=
    let j1 := canon_judgement j1 in
    let j2 := canon_judgement j2 in
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
