From Stdlib Require Import List Arith Utf8.
From Stdlib Require Import Lia FunctionalExtensionality List Relation_Operators.
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

Definition shift1 (t : tm) : tm := shift 1 0 t.

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

Lemma mapi_nth_error {A B : Type} (f : nat -> A -> B) (xs : list A) (i n : nat) (x : A) :
  nth_error xs n = Some x ->
  nth_error (mapi f xs i) n = Some (f (i + n) x).
Proof.
  revert i n.
  induction xs as [|x0 xs IH]; intros i n H; destruct n as [|n]; simpl in *.
  - discriminate.
  - discriminate.
  - inversion H; subst. simpl. now rewrite Nat.add_0_r.
  - apply (IH (S i) n) in H.
    (* align indices: S i + n = i + S n *)
    now rewrite Nat.add_succ_comm in H.
Qed.

Definition ctor_arg_tys (Σenv : Ty.env) (I c : nat) : option (list tm) :=
  match SP.lookup_ind Σenv I with
  | None => None
  | Some ΣI =>
      match SP.lookup_ctor ΣI c with
      | None => None
      | Some ctor =>
          Some (@SP.ctor_param_tys _ ctor ++ repeat (tInd I) (@SP.ctor_rec_arity _ ctor))
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
Fixpoint commute_branch_typed_rec
    (k : nat) (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br_acc : tm) : tm :=
  match argsTys with
  | [] => tCase J br_acc (shift k 0 D) (map (shift k 0) brsJ)
  | A :: argsTys' =>
      tLam (shift k 0 A)
        (commute_branch_typed_rec (S k) J D brsJ argsTys'
           (tApp (shift1 br_acc) (tVar 0)))
  end.

Definition commute_branch_typed (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm) : tm :=
  commute_branch_typed_rec 0 J D brsJ argsTys br.

Definition commute_case_case_once_typed (Σenv : Ty.env) (t : tm) : tm :=
  match t with
  | tCase j (tCase i (tVar x) C brsI) D brsJ =>
      let brsI' :=
        mapi
          (fun c br =>
             match ctor_arg_tys Σenv i c with
             | Some tys => commute_branch_typed j D brsJ tys br
             | None => br
             end)
          brsI 0
      in
      tCase i (tVar x) C brsI'
  | _ => t
  end.

(** Helper: lift a single step into `steps`. *)
Lemma steps_step (t u : tm) : step t u -> steps t u.
Proof.
  intro H.
  apply rt_step.
  exact H.
Qed.

Lemma steps_trans (t u v : tm) : steps t u -> steps u v -> steps t v.
Proof.
  intros Htu Huv.
  eapply rt_trans; eauto.
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
  intros [Hcase Hv].

  assert (Hdecomp : forall (t0 t : tm),
             steps t0 t ->
             forall (scrut0 : tm),
               t0 = tCase I scrut0 C brs ->
               (exists scrut1,
                   steps scrut0 scrut1 /\ t = tCase I scrut1 C brs)
               \/
               (exists c params recs br,
                   steps scrut0 (tRoll I c params recs)
                   /\ branch brs c = Some br
                   /\ steps (Cbn.apps br (params ++ recs)) t)).
  {
    intros t0 t Hsteps0.
    induction Hsteps0; intros scrut0 ->.
    - left.
      exists scrut0.
      split; [apply rt_refl|reflexivity].
    - (* single step *)
      inversion H; subst.
      + left.
        eexists.
        split.
        * apply steps_step. exact H0.
        * reflexivity.
      + right.
        do 4 eexists.
        split.
        * apply rt_refl.
        * split; [exact H0|].
          apply rt_refl.
    - (* trans *)
      specialize (IHHsteps0_1 scrut0 eq_refl).
      destruct IHHsteps0_1 as [Hl|Hr].
      + destruct Hl as [scrut1 [Hscrut01 ->]].
        specialize (IHHsteps0_2 scrut1 eq_refl).
        destruct IHHsteps0_2 as [Hl'|Hr'].
        * left.
          destruct Hl' as [scrut2 [Hscrut12 ->]].
          exists scrut2.
          split; [eapply steps_trans; eauto|reflexivity].
        * right.
          destruct Hr' as (c & params & recs & br & Hscrut1roll & Hbr & Happs).
          exists c, params, recs, br.
          split; [eapply steps_trans; eauto|].
          split; [exact Hbr|exact Happs].
      + right.
        destruct Hr as (c & params & recs & br & Hscrutroll & Hbr & Happs).
        exists c, params, recs, br.
        split; [exact Hscrutroll|].
        split; [exact Hbr|].
        eapply steps_trans; eauto.
  }

  specialize (Hdecomp (tCase I scrut C brs) v Hcase scrut eq_refl).
  destruct Hdecomp as [Hl|Hr].
  - destruct Hl as [scrut1 [_ ->]].
    exfalso. inversion Hv.
  - destruct Hr as (c & params & recs & br & Hscrutroll & Hbr & Happs).
    exists c, params, recs, br.
    split; [exact Hscrutroll|].
    split; [exact Hbr|].
    split; [exact Happs|exact Hv].
Qed.

Lemma terminates_to_steps_prefix (t u v : tm) :
  steps t u -> terminates_to t v -> terminates_to u v.
Proof.
  exact Cbn.terminates_to_steps_prefix.
Qed.

Lemma steps_apps_congr (t t' : tm) (us : list tm) :
  steps t t' -> steps (Cbn.apps t us) (Cbn.apps t' us).
Proof.
  exact Cbn.steps_apps_congr.
Qed.

Lemma steps_beta_apps (A : tm) (t u : tm) (us : list tm) :
  steps (Cbn.apps (tLam A t) (u :: us)) (Cbn.apps (subst0 u t) us).
Proof.
  simpl.
  eapply steps_apps_congr.
  apply steps_step.
  apply step_beta.
Qed.

Lemma shift0_id (t : tm) : shift 0 0 t = t.
Proof.
  unfold shift.
  assert (H : shift_sub 0 0 = fun x => x).
  { apply functional_extensionality; intro x.
    unfold shift_sub.
    destruct (x <? 0) eqn:Hx.
    - apply Nat.ltb_lt in Hx. lia.
    - lia. }
  rewrite H.
  asimpl.
Qed.

Lemma map_shift0_id (ts : list tm) : map (shift 0 0) ts = ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - reflexivity.
  - rewrite shift0_id. now rewrite IH.
Qed.

Lemma steps_commute_branch_typed
    (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br_acc : tm)
    (args : list tm) :
  length args = length argsTys ->
  steps (Cbn.apps (commute_branch_typed_rec 0 J D brsJ argsTys br_acc) args)
    (tCase J (Cbn.apps br_acc args) D brsJ).
Proof.
  revert br_acc args.
  induction argsTys as [|A argsTys IH]; intros br_acc args Hlen.
  - destruct args as [|u us]; simpl in Hlen; [|discriminate].
    cbn [commute_branch_typed_rec].
    rewrite shift0_id.
    rewrite map_shift0_id.
    apply rt_refl.
  - destruct args as [|u us]; simpl in Hlen; [discriminate|].
    inversion Hlen as [Hlen'].
    cbn [commute_branch_typed_rec].
    eapply steps_trans.
    + apply steps_beta_apps.
    + cbn [shift1].
      asimpl.
      change (Cbn.apps br_acc (u :: us)) with (Cbn.apps (tApp br_acc u) us).
      apply IH.
      exact Hlen'.
Qed.

(** The key lemma needed for CIU: applying the eta-expanded branch is
    observationally the same as applying the original branch and then casing. *)
Lemma terminates_to_commute_branch_typed
    (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm)
    (args : list tm) (v : tm) :
  length args = length argsTys ->
  terminates_to (Cbn.apps (commute_branch_typed J D brsJ argsTys br) args) v
  <->
  terminates_to (tCase J (Cbn.apps br args) D brsJ) v.
Proof.
  intro Hlen.
  pose proof (steps_commute_branch_typed J D brsJ argsTys br args Hlen) as Hsteps.
  split.
  - intro Hterm.
    eapply terminates_to_steps_prefix; eauto.
  - intro Hterm.
    destruct Hterm as [Hcase Hv].
    split.
    + eapply steps_trans; eauto.
    + exact Hv.
Qed.

Lemma steps_case_to_apps
    (I : nat) (scrut C : tm) (brs : list tm)
    (c : nat) (params recs : list tm) (br : tm) :
  steps scrut (tRoll I c params recs) ->
  branch brs c = Some br ->
  steps (tCase I scrut C brs) (Cbn.apps br (params ++ recs)).
Proof.
  exact Cbn.steps_case_to_apps.
Qed.


Lemma steps_to_value_unique (t u v : tm) :
  steps t v -> value v -> steps t u -> steps u v.
Proof.
  exact Cbn.steps_to_value_unique.
Qed.


Lemma shift1_tInd (I : nat) : shift1 (tInd I) = tInd I.
Proof.
  reflexivity.
Qed.

Lemma subst_list_tInd (σ : list tm) (I : nat) : Ty.subst_list σ (tInd I) = tInd I.
Proof.
  reflexivity.
Qed.

Lemma steps_from_value_eq (v t : tm) :
  value v -> steps v t -> t = v.
Proof.
  intros Hv Hsteps.
  induction Hsteps.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
  - etransitivity; eauto.
Qed.

Lemma shift1_inj_tInd (t : tm) (I : nat) :
  shift1 t = tInd I -> t = tInd I.
Proof.
  destruct t; cbn [shift1 shift]; intro H; try discriminate.
  exact H.
Qed.

Lemma subst_list_var_of_nth (σ : list tm) (x : nat) (u : tm) :
  nth_error σ x = Some u ->
  Ty.subst_list σ (tVar x) = u.
Proof.
  intro Hx.
  unfold Ty.subst_list, Ty.subst_sub.
  unfold Typing.Typing.subst_list, Typing.Typing.subst_sub, Typing.Typing.sub_fun.
  cbn [Term.Syntax.subst].
  rewrite Hx.
  reflexivity.
Qed.

Lemma has_subst_nth_tInd
    (Σenv : Ty.env) (Δ : Ty.ctx) (σ : list tm) (Γ : Ty.ctx) (x I : nat) :
  Ty.has_subst Σenv Δ σ Γ ->
  Ty.ctx_lookup Γ x = Some (tInd I) ->
  exists u,
    nth_error σ x = Some u /\ Ty.has_type Σenv Δ u (tInd I).
Proof.
  intro Hs.
  revert x I.
  induction Hs as [|Γ0 A0 σ0 u0 Hs IH Htyu]; intros x I Hlookup.
  - cbn [Ty.ctx_lookup] in Hlookup. discriminate.
  - destruct x as [|x].
    + cbn [Ty.ctx_lookup] in Hlookup.
      apply shift1_inj_tInd in Hlookup.
      subst A0.
      exists u0.
      split; [reflexivity|].
      cbn in Htyu.
      now rewrite subst_list_tInd in Htyu.
    + cbn [Ty.ctx_lookup] in Hlookup.
      destruct (Ty.ctx_lookup Γ0 x) as [T|] eqn:HT; cbn in Hlookup; try discriminate.
      inversion Hlookup; subst.
      apply shift1_inj_tInd in H1.
      subst T.
      destruct (IH x I HT) as (u & Hnth & Hty).
      exists u.
      split; [exact Hnth|exact Hty].
Qed.

Lemma value_has_type_tInd_inv
    (Σenv : Ty.env) (Γ : Ty.ctx) (v : tm) (I : nat) :
  value v -> Ty.has_type Σenv Γ v (tInd I) ->
  exists ΣI ctor c params recs,
    v = tRoll I c params recs
    /\ SP.lookup_ind Σenv I = Some ΣI
    /\ SP.lookup_ctor ΣI c = Some ctor
    /\ Forall2 (Ty.has_type Σenv Γ) params (@SP.ctor_param_tys _ ctor)
    /\ Forall (fun r => Ty.has_type Σenv Γ r (tInd I)) recs
    /\ length recs = (@SP.ctor_rec_arity _ ctor).
Proof.
  intros Hv Hty.
  inversion Hv; subst.
  - inversion Hty; subst; discriminate.
  - inversion Hty; subst.
    exists ΣI, ctor, c, params, recs.
    repeat split; eauto.
Qed.

Lemma branch_map_subst (σ : list tm) (brs : list tm) (c : nat) :
  branch (map (Ty.subst_list σ) brs) c = option_map (Ty.subst_list σ) (branch brs c).
Proof.
  unfold branch.
  rewrite nth_error_map.
  reflexivity.
Qed.

Lemma subst_list_shift0 (σ : list tm) (t : tm) :
  Ty.subst_list σ (shift 0 0 t) = shift 0 0 (Ty.subst_list σ t).
Proof.
  unfold Ty.subst_list, Ty.subst_sub.
  unfold Typing.Typing.subst_list, Typing.Typing.subst_sub.
  unfold shift.
  asimpl.
Qed.

Lemma subst_list_commute_branch_typed
    (σ : list tm)
    (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm) :
  Ty.subst_list σ (commute_branch_typed J D brsJ argsTys br) =
  commute_branch_typed J (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) (map (Ty.subst_list σ) argsTys) (Ty.subst_list σ br).
Proof.
  unfold commute_branch_typed.
  revert br.
  induction argsTys as [|A argsTys IH]; intro br0.
  - cbn [commute_branch_typed_rec].
    cbn.
    f_equal.
    + reflexivity.
    + now rewrite subst_list_shift0.
    + rewrite map_map.
      apply map_ext.
      intro br1.
      now rewrite subst_list_shift0.
  - cbn [commute_branch_typed_rec].
    cbn.
    f_equal.
    + now rewrite subst_list_shift0.
    + asimpl.
      apply IH.
Qed.

(** CIU preservation for the judgement-driven rewrite. *)
Theorem ciu_jTy_commute_case_case_once (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  Ty.has_type Σenv Γ t A ->
  CIUJudgement.ciu_jTy Σenv Γ t (commute_case_case_once_typed Σenv t) A.
Proof.
  intro Hty.

  (* Only the nested-case shape is rewritten. *)
  destruct t as
    [x|s|A0 B0|A0 t0|t1 t2|A0 t0|I0|I0 c0 ps0 rs0|j scrut D brsJ];
    cbn [commute_case_case_once_typed];
    try (apply CIUJudgement.ciu_jTy_of_eq; reflexivity).

  destruct scrut as
    [x1|s1|A1 B1|A1 t3|t3 t4|A1 t3|I1|I1 c1 ps1 rs1|i scrut2 C brsI];
    cbn [commute_case_case_once_typed];
    try (apply CIUJudgement.ciu_jTy_of_eq; reflexivity).

  destruct scrut2 as
    [x2|s2|A2 B2|A2 t5|t5 t6|A2 t5|I2|I2 c2 ps2 rs2|I2 scrut3 C2 brs2];
    cbn [commute_case_case_once_typed];
    try (apply CIUJudgement.ciu_jTy_of_eq; reflexivity).

  (* Now: t = case j (case i (var x1) C brsI) D brsJ *)
  rename x1 into x.

  (* Invert typing twice. *)
  inversion Hty as
    [| | | | | | | |Γ0 j0 ΣJ scrutTy Dty brsTy iSort HjΣ Hjlen HjScrut HjD Hjbrs];
    subst.
  inversion HjScrut as
    [| | | | | | | |Γ1 i0 ΣI scrutTyI Cty brsTyI iSortI HiΣ Hilen Hivar HcTy Hib];
    subst.
  inversion Hivar as [Γ2 x0 Avar Hctx]; subst.

  (* The inner case has type `C`, but is used as a `tInd j` scrutinee. *)
  assert (HC : C = tInd j).
  { inversion HjScrut; subst; reflexivity. }
  subst C.

  unfold CIUJudgement.ciu_jTy.
  split.
  - (* forward direction *)
    intros Δ σ v Hσ Hvσ Hterm.

    (* Determine σ(x) and its roll shape from typing + value restriction. *)
    destruct (has_subst_nth_tInd Σenv Δ σ Γ x i Hσ Hctx) as (ux & Hnthx & Htyx).
    pose proof (subst_list_var_of_nth σ x ux Hnthx) as Hsubx.
    pose proof (Forall_nth_error _ _ _ Hvσ Hnthx) as Hvux.

    destruct (value_has_type_tInd_inv Σenv Δ ux i Hvux Htyx)
      as (ΣIx & ctor & c & params & recs & Hux & HiΣx & Hctor & Hparams & Hrecs & Hreclen).
    subst ux.

    (* The selected inner branch exists (from typing of the inner case). *)
    destruct (Hib c ctor Hctor) as (brI & HbrI & HtyBrI).

    set (tys := @SP.ctor_param_tys _ ctor ++ repeat (tInd i) (@SP.ctor_rec_arity _ ctor)).
    assert (Hlen_args : length (params ++ recs) = length tys).
    { subst tys.
      rewrite app_length.
      rewrite Forall2_length in Hparams.
      rewrite Hparams.
      rewrite repeat_length.
      lia. }

    assert (Hargtys : ctor_arg_tys Σenv i c = Some tys).
    { unfold ctor_arg_tys.
      rewrite HiΣ.
      rewrite Hctor.
      reflexivity. }

    (* Unfold the substituted original term and rewrite σ(x) to the roll. *)
    cbn [Ty.subst_list Ty.subst_sub] in Hterm.
    rewrite Hsubx in Hterm.
    rewrite subst_list_tInd in Hterm.

    (* Inner case steps to the chosen branch application immediately. *)
    assert (Hinner_to_apps : steps
              (tCase i (tRoll i c params recs) (tInd j) (map (Ty.subst_list σ) brsI))
              (Cbn.apps (Ty.subst_list σ brI) (params ++ recs))).
    {
      eapply steps_case_to_apps.
      - apply rt_refl.
      - (* branch lookup in substituted list *)
        rewrite branch_map_subst.
        rewrite HbrI.
        cbn.
        reflexivity.
    }

    (* Lift this scrutinee step under the outer case. *)
    assert (Houter_to_mid : steps
              (tCase j (tCase i (tRoll i c params recs) (tInd j) (map (Ty.subst_list σ) brsI))
                 (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ))
              (tCase j (Cbn.apps (Ty.subst_list σ brI) (params ++ recs))
                 (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ))).
    {
      apply Cbn.steps_case_scrut_congr.
      exact Hinner_to_apps.
    }

    (* From termination of the original term, infer termination of the mid case. *)
    assert (Hmid : terminates_to
        (tCase j (Cbn.apps (Ty.subst_list σ brI) (params ++ recs))
           (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ)) v).
    { eapply terminates_to_steps_prefix; eauto. }

    (* Commute the outer case into the branch application.
       Note: after substitution, the branch transform's type list is `map (subst_list σ) tys`. *)
    set (tysσ := map (Ty.subst_list σ) tys).
    assert (Hlen_argsσ : length (params ++ recs) = length tysσ).
    { subst tysσ. now rewrite map_length. }

    assert (Happ_comm : terminates_to
        (Cbn.apps (commute_branch_typed j (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) tysσ (Ty.subst_list σ brI))
           (params ++ recs)) v).
    {
      apply (proj2 (terminates_to_commute_branch_typed j (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) tysσ (Ty.subst_list σ brI)
                     (params ++ recs) v Hlen_argsσ)).
      exact Hmid.
    }

    (* Identify the transformed branch at index c. *)
    set (brsI' :=
           mapi
             (fun c0 br =>
                match ctor_arg_tys Σenv i c0 with
                | Some tys0 => commute_branch_typed j D brsJ tys0 br
                | None => br
                end) brsI 0).

    assert (HbrI' : branch brsI' c = Some (commute_branch_typed j D brsJ tys brI)).
    {
      unfold brsI'.
      unfold branch.
      pose proof (mapi_nth_error
                    (fun c0 br =>
                       match ctor_arg_tys Σenv i c0 with
                       | Some tys0 => commute_branch_typed j D brsJ tys0 br
                       | None => br
                       end)
                    brsI 0 c brI HbrI) as Hnth.
      cbn in Hnth.
      rewrite Hargtys in Hnth.
      exact Hnth.
    }

    (* The transformed term also steps to the commuting-branch application. *)
    assert (Hsteps_transformed : steps
              (tCase i (tRoll i c params recs) (tInd j) (map (Ty.subst_list σ) brsI'))
              (Cbn.apps (Ty.subst_list σ (commute_branch_typed j D brsJ tys brI)) (params ++ recs))).
    {
      eapply steps_case_to_apps.
      - apply rt_refl.
      - rewrite branch_map_subst.
        rewrite HbrI'.
        cbn.
        reflexivity.
    }

    (* Rewrite the substituted commuting branch to the commuting branch of substituted parts. *)
    assert (Hsub_branch : Ty.subst_list σ (commute_branch_typed j D brsJ tys brI) =
                          commute_branch_typed j (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) tysσ (Ty.subst_list σ brI)).
    {
      rewrite (subst_list_commute_branch_typed σ j D brsJ tys brI).
      unfold tysσ.
      reflexivity.
    }

    (* Conclude by prefixing the steps from the transformed term. *)
    eapply terminates_to_steps_prefix.
    + exact Hsteps_transformed.
    + rewrite Hsub_branch.
      exact Happ_comm.

  - (* backward direction *)
    intros Δ σ v Hσ Hvσ Hterm.

    destruct (has_subst_nth_tInd Σenv Δ σ Γ x i Hσ Hctx) as (ux & Hnthx & Htyx).
    pose proof (subst_list_var_of_nth σ x ux Hnthx) as Hsubx.
    pose proof (Forall_nth_error _ _ _ Hvσ Hnthx) as Hvux.

    destruct (value_has_type_tInd_inv Σenv Δ ux i Hvux Htyx)
      as (ΣIx & ctor & c & params & recs & Hux & HiΣx & Hctor & Hparams & Hrecs & Hreclen).
    subst ux.

    destruct (Hib c ctor Hctor) as (brI & HbrI & HtyBrI).

    set (tys := @SP.ctor_param_tys _ ctor ++ repeat (tInd i) (@SP.ctor_rec_arity _ ctor)).
    assert (Hlen_args : length (params ++ recs) = length tys).
    { subst tys.
      rewrite app_length.
      rewrite Forall2_length in Hparams.
      rewrite Hparams.
      rewrite repeat_length.
      lia. }

    set (tysσ := map (Ty.subst_list σ) tys).
    assert (Hlen_argsσ : length (params ++ recs) = length tysσ).
    { subst tysσ. now rewrite map_length. }

    assert (Hargtys : ctor_arg_tys Σenv i c = Some tys).
    { unfold ctor_arg_tys.
      rewrite HiΣ.
      rewrite Hctor.
      reflexivity. }

    (* Normalize the substituted transformed term. *)
    cbn [Ty.subst_list Ty.subst_sub] in Hterm.
    rewrite Hsubx in Hterm.
    rewrite subst_list_tInd in Hterm.

    (* Identify the transformed branch at index c. *)
    set (brsI' :=
           mapi
             (fun c0 br =>
                match ctor_arg_tys Σenv i c0 with
                | Some tys0 => commute_branch_typed j D brsJ tys0 br
                | None => br
                end) brsI 0).

    assert (HbrI' : branch brsI' c = Some (commute_branch_typed j D brsJ tys brI)).
    {
      unfold brsI'.
      unfold branch.
      pose proof (mapi_nth_error
                    (fun c0 br =>
                       match ctor_arg_tys Σenv i c0 with
                       | Some tys0 => commute_branch_typed j D brsJ tys0 br
                       | None => br
                       end)
                    brsI 0 c brI HbrI) as Hnth.
      cbn in Hnth.
      rewrite Hargtys in Hnth.
      exact Hnth.
    }

    (* Invert termination of the transformed case: it must take the case-roll step. *)
    destruct (terminates_to_case_inv i (tRoll i c params recs) (tInd j) (map (Ty.subst_list σ) brsI') v Hterm)
      as (c' & params' & recs' & brσ & Hscrut & Hbrσ & Happσ).

    (* Since the scrutinee is already a value roll, it cannot change. *)
    assert (Heqroll : tRoll i c params recs = tRoll i c' params' recs').
    {
      apply (steps_from_value_eq (tRoll i c params recs) (tRoll i c' params' recs')).
      - apply v_roll.
      - exact Hscrut.
    }
    inversion Heqroll; subst c' params' recs'.

    (* The selected branch is exactly the substituted commuting branch. *)
    assert (Hbrσ_eq : brσ = Ty.subst_list σ (commute_branch_typed j D brsJ tys brI)).
    {
      rewrite branch_map_subst in Hbrσ.
      rewrite HbrI' in Hbrσ.
      cbn in Hbrσ.
      inversion Hbrσ.
      reflexivity.
    }
    subst brσ.

    (* Rewrite the substituted commuting branch to the commuting branch of substituted parts. *)
    assert (Hsub_branch : Ty.subst_list σ (commute_branch_typed j D brsJ tys brI) =
                          commute_branch_typed j (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) tysσ (Ty.subst_list σ brI)).
    {
      rewrite (subst_list_commute_branch_typed σ j D brsJ tys brI).
      unfold tysσ.
      reflexivity.
    }

    (* Hence the outer case on the branch application terminates too. *)
    assert (Hmid : terminates_to
        (tCase j (Cbn.apps (Ty.subst_list σ brI) (params ++ recs))
           (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ)) v).
    {
      (* Use the iff in the commuting-branch lemma. *)
      apply (proj1 (terminates_to_commute_branch_typed j (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) tysσ (Ty.subst_list σ brI)
                     (params ++ recs) v Hlen_argsσ)).
      rewrite <- Hsub_branch.
      exact Happσ.
    }

    (* The original nested case steps to that mid case (by reducing the inner case to apps). *)
    assert (Hinner_to_apps : steps
              (tCase i (tRoll i c params recs) (tInd j) (map (Ty.subst_list σ) brsI))
              (Cbn.apps (Ty.subst_list σ brI) (params ++ recs))).
    {
      eapply steps_case_to_apps.
      - apply rt_refl.
      - rewrite branch_map_subst.
        rewrite HbrI.
        cbn.
        reflexivity.
    }

    assert (Houter_to_mid : steps
              (tCase j (tCase i (tRoll i c params recs) (tInd j) (map (Ty.subst_list σ) brsI))
                 (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ))
              (tCase j (Cbn.apps (Ty.subst_list σ brI) (params ++ recs))
                 (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ))).
    {
      apply Cbn.steps_case_scrut_congr.
      exact Hinner_to_apps.
    }

    eapply terminates_to_steps_prefix; eauto.
Qed.

(** A reference-level cyclic-proof transform implemented by extract/re-read-off.

    This is *not* the final in-graph rewrite, but it gives a concrete function to
    target with equivalence-preservation theorems first.
*)
Definition commute_case_case_raw (Σenv : Ty.env) (t : tm) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv t).

Definition commute_case_case_builder (Σenv : Ty.env) (b : RO.builder) (root : nat) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv (EX.extract b root)).
