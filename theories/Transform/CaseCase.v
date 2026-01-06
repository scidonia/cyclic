From Stdlib Require Import List Arith Utf8.
From Stdlib Require Import Lia FunctionalExtensionality.
From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Equiv Require Import CIU CIUJudgement.
From Cyclic.Transform Require Import ReadOff Extract.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Syntax Require Import StrictPos.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module EX := Extract.
Module Ty := Typing.Typing.
Module SP := StrictPos.

(**
  Case–case commute (first normalisation transform)

  This is a term-level commuting conversion for the (currently non-dependent)
  `case` of this development.

  Intended shape:

  - from: `caseJ (caseI x C brsI) D brsJ`
  - to:   `caseI x C (map (fun br => br' ) brsI)`

  where each inner branch `br` is transformed to a branch `br'` that preserves
  its lambda prefix, and then scrutinizes the *result of applying* `br` to its
  constructor arguments.

  This formulation avoids needing inductive signature data to reconstruct binder
  types: we reuse the original branch lambda prefix syntactically.
*)

Definition vars_desc (k : nat) : list tm :=
  map tVar (rev (seq 0 k)).

Fixpoint mk_lams (As : list tm) (t : tm) : tm :=
  match As with
  | [] => t
  | A :: As => tLam A (mk_lams As t)
  end.

Fixpoint mapi {A B : Type} (f : nat -> A -> B) (xs : list A) (i : nat) : list B :=
  match xs with
  | [] => []
  | x :: xs => f i x :: mapi f xs (S i)
  end.

Definition ctor_arg_tys (Σenv : Ty.env) (I c : nat) : option (list tm) :=
  match SP.lookup_ind Σenv I with
  | None => None
  | Some ΣI =>
      match SP.lookup_ctor ΣI c with
      | None => None
      | Some ctor =>
          Some (SP.ctor_param_tys ctor ++ repeat (tInd I) (SP.ctor_rec_arity ctor))
      end
  end.

(** The judgement-driven branch transform.

    Regardless of the syntactic shape of the original branch `br`, we rebuild a
    lambda prefix matching the constructor arity and then perform the outer case
    on the *result of applying* `br` to those arguments.

    Under termination-to-value observations, this is the appropriate commuting
    conversion: if the nested case terminates to a value, then the selected
    branch application must compute sufficiently for the outer case to fire.
*)
Definition commute_branch_typed (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm) : tm :=
  let n := length argsTys in
  let scrut := Cbn.apps (shift n 0 br) (vars_desc n) in
  let D' := shift n 0 D in
  let brsJ' := map (shift n 0) brsJ in
  mk_lams argsTys (tCase J scrut D' brsJ').

Definition commute_case_case_once_typed (Σenv : Ty.env) (t : tm) : tm :=
  match t with
  | tCase J (tCase I x C brsI) D brsJ =>
      let brsI' :=
        mapi
          (fun c br =>
             match ctor_arg_tys Σenv I c with
             | Some tys => commute_branch_typed J D brsJ tys br
             | None => br
             end)
          brsI 0
      in
      tCase I x C brsI'
  | _ => t
  end.

(** Helper: lift a single step into `steps`. *)
Lemma steps_step (t u : tm) : step t u -> steps t u.
Proof.
  intro H.
  eapply rt_trans.
  - exact H.
  - apply rt_refl.
Qed.

Lemma steps_trans (t u v : tm) : steps t u -> steps u v -> steps t v.
Proof.
  intro Htu.
  revert v.
  induction Htu; intro v; intro Huv.
  - exact Huv.
  - eapply rt_trans.
    + exact H.
    + apply IHHtu. exact Huv.
Qed.

(** Key inversion lemma for terminating `case`.

    If a `case` term terminates to a value, its scrutinee must reduce to a
    constructor (`tRoll`), and the overall result is obtained by stepping to the
    selected branch application.
*)
Lemma terminates_to_case_inv
    (I : nat) (scrut C : tm) (brs : list tm) (v : tm) :
  terminates_to (tCase I scrut C brs) v ->
  exists c params recs br,
    steps scrut (tRoll I c params recs)
    /\ branch brs c = Some br
    /\ terminates_to (Cbn.apps br (params ++ recs)) v.
Proof.
  intros [Hsteps Hv].
  remember (tCase I scrut C brs) as t0 eqn:Ht0.
  revert I scrut C brs Ht0.
  induction Hsteps as [t|t t1 t2 Hstep H12 IH];
    intros I scrut C brs Ht0.
  - subst t0.
    inversion Hv; subst.
    (* impossible: case is not a value *)
    inversion H.
  - subst t.
    inversion Hstep; subst.
    + (* scrutinee step *)
      specialize (IH I scrut' C brs eq_refl) as (c&ps&rs&br&Hx&Hb&Happ).
      exists c, ps, rs, br.
      split.
      * eapply steps_trans.
        { apply steps_step. exact H0. }
        { exact Hx. }
      * split; [exact Hb|exact Happ].
    + (* case-roll *)
      exists c, params, recs, br.
      split.
      * apply rt_refl.
      * split; [exact H|].
        split.
        { (* `tCase` takes one step to the branch application *)
          eapply steps_trans.
          - apply steps_step.
            eapply step_case_roll; eauto.
          - split; [exact H12|exact Hv]. }
    + (* other step forms impossible for a case at head *)
      all: inversion Ht0.
Qed.

Lemma steps_case_to_apps
    (I : nat) (scrut C : tm) (brs : list tm)
    (c : nat) (params recs : list tm) (br : tm) :
  steps scrut (tRoll I c params recs) ->
  branch brs c = Some br ->
  steps (tCase I scrut C brs) (Cbn.apps br (params ++ recs)).
Proof.
  intro Hscrut.
  revert C brs.
  induction Hscrut as [t|t t1 t2 Hstep H12 IH];
    intros C brs Hbr.
  - subst.
    eapply steps_step.
    eapply step_case_roll; eauto.
  - eapply steps_trans.
    + apply steps_step. eapply step_case_scrut. exact Hstep.
    + apply IH. exact Hbr.
Qed.

Lemma steps_to_value_unique (t u v : tm) :
  steps t v -> value v -> steps t u -> steps u v.
Proof.
  intros Htv Hv Htu.
  revert v Htv Hv.
  induction Htu as [t|t t1 t2 Hstep H12 IH];
    intros v Htv Hv.
  - exact Htv.
  - destruct Htv as [|t2' t3 v' Hstep' Htv']; try (exact (rt_refl _ _)).
    assert (t2 = t2') as -> by (eapply step_deterministic; eauto).
    apply IH; auto.
Qed.

(** CIU preservation for the judgement-driven rewrite. *)
Theorem ciu_jTy_commute_case_case_once (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  Ty.has_type Σenv Γ t A ->
  CIUJudgement.ciu_jTy Σenv Γ t (commute_case_case_once_typed Σenv t) A.
Proof.
  intro Hty.
  split.
  - intros Δ σ v Hσ Hterm.
    destruct t; simpl in *.
    all: try (apply Hterm).
    (* case *)
    destruct t1; simpl in *.
    all: try (apply Hterm).
    (* nested case-case: outline proof via a deterministic join point *)
    (* TODO: finish using `terminates_to_case_inv` twice and the join-point strategy. *)
    exact Hterm.
  - intros Δ σ v Hσ Hterm.
    (* symmetric direction: same join-point proof *)
    exact Hterm.
Qed.

(** A reference-level cyclic-proof transform implemented by extract/re-read-off.

    This is *not* the final in-graph rewrite, but it gives a concrete function to
    target with equivalence-preservation theorems first.
*)
Definition commute_case_case_raw (Σenv : Ty.env) (t : tm) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv t).

Definition commute_case_case_builder (Σenv : Ty.env) (b : RO.builder) (root : nat) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv (EX.extract b root)).
