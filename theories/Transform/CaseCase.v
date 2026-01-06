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
  - inversion H; subst. simpl. now rewrite Nat.add_0_r.
  - discriminate.
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
Fixpoint commute_branch_typed_rec (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br_acc : tm) : tm :=
  match argsTys with
  | [] => tCase J br_acc D brsJ
  | A :: argsTys' =>
      tLam A
        (commute_branch_typed_rec J (shift1 D) (map shift1 brsJ) (map shift1 argsTys')
           (tApp (shift1 br_acc) (tVar 0)))
  end.

Definition commute_branch_typed (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm) : tm :=
  commute_branch_typed_rec J D brsJ argsTys br.

Definition commute_case_case_once_typed (Σenv : Ty.env) (t : tm) : tm :=
  match t with
  | tCase J (tCase I (tVar x) C brsI) D brsJ =>
      let brsI' :=
        mapi
          (fun c br =>
             match ctor_arg_tys Σenv I c with
             | Some tys => commute_branch_typed J D brsJ tys br
             | None => br
             end)
          brsI 0
      in
      tCase I (tVar x) C brsI'
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

Lemma terminates_to_steps_prefix (t u v : tm) :
  steps t u -> terminates_to t v -> terminates_to u v.
Proof.
  intros Htu [Htv Hv].
  split.
  - eapply steps_to_value_unique; eauto.
  - exact Hv.
Qed.

Lemma steps_apps_congr (t t' : tm) (us : list tm) :
  steps t t' -> steps (Cbn.apps t us) (Cbn.apps t' us).
Proof.
  intro H.
  revert t t' H.
  induction us as [|u us IH]; intros t t' H.
  - exact H.
  - simpl. (* apps t (u::us) = apps (tApp t u) us *)
    apply IH.
    clear IH.
    (* lift steps through app1 *)
    induction H as [x|x y z Hxy Hyz IH'];
      [apply rt_refl|].
    eapply rt_trans.
    + apply step_app1. exact Hxy.
    + exact IH'.
Qed.

Lemma steps_beta_apps (A : tm) (t u : tm) (us : list tm) :
  steps (Cbn.apps (tLam A t) (u :: us)) (Cbn.apps (subst0 u t) us).
Proof.
  simpl.
  (* reduce the head beta redex inside the application spine *)
  eapply steps_apps_congr.
  apply steps_step.
  apply step_beta.
Qed.

(** The key lemma needed for CIU: applying the eta-expanded branch is
    observationally the same as applying the original branch and then casing. *)
Lemma terminates_to_commute_branch_typed
    (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm)
    (args : list tm) (v : tm) :
  length args = length argsTys ->
  terminates_to (Cbn.apps (commute_branch_typed J D brsJ argsTys br) args) v
  <>
  terminates_to (tCase J (Cbn.apps br args) D brsJ) v.
Proof.
  revert D brsJ br args v.
  induction argsTys as [|A tys IH];
    intros D brsJ br args v Hlen.
  - destruct args; simpl in Hlen; [|discriminate].
    subst.
    simpl. (* no binders *)
    tauto.
  - destruct args as [|u us]; simpl in Hlen; [discriminate|].
    inversion Hlen as [Hlen'].
    specialize (IH (shift1 D) (map shift1 brsJ) (tApp (shift1 br) (tVar 0)) us v Hlen').
    split.
    + intro Hterm.
      (* one beta step peels the lambda prefix *)
      assert (Hstep :
        steps (Cbn.apps (commute_branch_typed J D brsJ (A :: tys) br) (u :: us))
              (Cbn.apps (subst0 u (commute_branch_typed_rec J (shift1 D) (map shift1 brsJ)
                                   (map shift1 tys) (tApp (shift1 br) (tVar 0)))) us)).
      { unfold commute_branch_typed.
        simpl.
        apply steps_beta_apps. }
      (* transport termination across the prefix step *)
      pose proof (terminates_to_steps_prefix _ _ _ Hstep Hterm) as Hterm'.
      (* simplify the substituted body: it is the same recursive commute with br u *)
      (* This is purely Autosubst computation. *)
      replace (subst0 u (commute_branch_typed_rec J (shift1 D) (map shift1 brsJ)
                         (map shift1 tys) (tApp (shift1 br) (tVar 0))))
        with (commute_branch_typed_rec J D brsJ tys (tApp br u)) in Hterm'
        by (cbn; asimpl; reflexivity).
      (* apply the IH *)
      apply (IH) in Hterm'.
      (* relate apps br (u::us) with apps (tApp br u) us *)
      simpl in Hterm'.
      exact Hterm'.
    + intro Hterm.
      (* converse direction: peel beta prefix on the left *)
      (* reduce the goal to the recursive case via IH, then prepend the beta step *)
      assert (Hterm' : terminates_to (Cbn.apps (commute_branch_typed_rec J D brsJ tys (tApp br u)) us) v).
      { (* use IH backwards *)
        (* apps br (u::us) = apps (tApp br u) us *)
        change (terminates_to (tCase J (Cbn.apps (tApp br u) us) D brsJ) v) in Hterm.
        apply (IH). exact Hterm. }
      (* now show the original left term steps to that recursive form in one beta *)
      assert (Hstep :
        steps (Cbn.apps (commute_branch_typed J D brsJ (A :: tys) br) (u :: us))
              (Cbn.apps (commute_branch_typed_rec J D brsJ tys (tApp br u)) us)).
      { unfold commute_branch_typed.
        simpl.
        (* beta-reduce first binder and simplify *)
        eapply steps_trans.
        - apply steps_beta_apps.
        - apply rt_refl. }
      split.
      - eapply steps_trans.
        + exact Hstep.
        + exact (proj1 Hterm').
      - exact (proj2 Hterm').
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

Lemma shift1_tInd (I : nat) : shift1 (tInd I) = tInd I.
Proof.
  reflexivity.
Qed.

Lemma subst_list_tInd (σ : list tm) (I : nat) : Ty.subst_list σ (tInd I) = tInd I.
Proof.
  reflexivity.
Qed.

(** Lookup lemma for typed substitutions at an inductive type.

    We only need the case where the looked-up type is `tInd I`, which is closed
    (hence stable under shifting/substitution).
*)
Lemma has_subst_lookup_tInd
    (Σenv : Ty.env) (Δ : Ty.ctx) (σ : list tm) (Γ : Ty.ctx) (x I : nat) (u : tm) :
  Ty.has_subst Σenv Δ σ Γ ->
  Ty.ctx_lookup Γ x = Some (tInd I) ->
  nth_error σ x = Some u ->
  Ty.has_type Σenv Δ u (tInd I).
Proof.
  intro Hσ.
  revert x I u.
  induction Hσ as [|Γ' A σ' u0 Hσ IH Htyu0]; intros x I u Hlookup Hnth; simpl in *.
  - destruct x; discriminate.
  - destruct x as [|x].
    + inversion Hnth; subst.
      (* ctx_lookup (A::Γ') 0 = Some (shift1 A) *)
      simpl in Hlookup.
      (* use that `tInd` is closed, so shift/subst do nothing *)
      rewrite subst_list_tInd.
      exact (eq_ind _ (fun Ty0 => Ty.has_type Σenv Δ u0 Ty0) Htyu0 _ (eq_sym Hlookup)).
    + (* tail *)
      simpl in Hlookup.
      destruct (Ty.ctx_lookup Γ' x) as [A'|] eqn:Hx; try discriminate.
      simpl in Hlookup.
      (* option_map shift1 ... = Some (tInd I) *)
      inversion Hlookup; subst.
      eapply IH.
      * exact Hx.
      * exact Hnth.
Qed.

(** Canonical forms for values at an inductive type. *)
Lemma value_has_type_tInd_roll
    (Σenv : Ty.env) (Δ : Ty.ctx) (v : tm) (I : nat) :
  value v ->
  Ty.has_type Σenv Δ v (tInd I) ->
  exists ΣI ctor c params recs,
    v = tRoll I c params recs
    /\ SP.lookup_ind Σenv I = Some ΣI
    /\ SP.lookup_ctor ΣI c = Some ctor
    /\ length params = length (SP.ctor_param_tys ctor)
    /\ length recs = SP.ctor_rec_arity ctor.
Proof.
  intros Hv Hty.
  inversion Hv; subst.
  - (* lambda can't have inductive type *)
    inversion Hty.
  - (* roll *)
    inversion Hty; subst.
    exists ΣI, ctor, c, params, recs.
    repeat split; try assumption.
    + (* params length from Forall2 *)
      now eapply Forall2_length.
Qed.

(** CIU preservation for the judgement-driven rewrite. *)
Theorem ciu_jTy_commute_case_case_once (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  Ty.has_type Σenv Γ t A ->
  CIUJudgement.ciu_jTy Σenv Γ t (commute_case_case_once_typed Σenv t) A.
Proof.
  intro Hty.
  split.
  - (* forward: original -> commuted *)
    intros Δ σ v Hσ Hvσ Hterm.
    destruct t as [x|i|A1 B|A1 t1|t1 t2|A1 t1|I1|I1 c1 ps1 rs1|I1 scrut1 C1 brs1];
      simpl in *; try exact Hterm.
    destruct scrut1 as [x0|i0|A2 B2|A2 t2'|t2' u2|A2 t2'|I2|I2 c2 ps2 rs2|I2 scrut2 C2 brs2];
      simpl in *; try exact Hterm.
    destruct scrut2 as [xvar| | | | | | | | ]; try exact Hterm.
    assert (Hxlen : xvar < length σ).
    { rewrite (Ty.has_subst_length _ _ _ _ Hσ).
      inversion Hty; subst; try lia.
      inversion H4; subst; try lia.
      inversion H6; subst.
      eapply Ty.ctx_lookup_lt; eauto. }
    destruct (nth_error σ xvar) as [u|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
    inversion Hty; subst.
    inversion H4; subst.
    inversion H6; subst.
    pose proof (has_subst_lookup_tInd Σenv Δ σ Γ xvar I2 u Hσ H8 Hnth) as Hut.
    pose proof (Forall_nth_error _ _ _ Hvσ Hnth) as Hvalu.
    destruct (value_has_type_tInd_roll Σenv Δ u I2 Hvalu Hut)
      as (ΣI&ctor&c&params&recs&->&HΣI&Hctor&Hlenp&Hlenr).
    unfold ctor_arg_tys.
    rewrite HΣI, Hctor.
    set (tys := SP.ctor_param_tys ctor ++ repeat (tInd I2) (SP.ctor_rec_arity ctor)).
    assert (Hargslen : length (params ++ recs) = length tys).
    { subst tys. rewrite app_length, repeat_length. lia. }
    assert (HbrI : exists brI, branch brs2 c = Some brI).
    { inversion H4; subst.
      specialize (H12 c ctor Hctor) as (brI&Hb&HTybrI).
      exists brI. exact Hb. }
    destruct HbrI as [brI HbI].
    assert (HbI' :
      branch (mapi (fun c0 br0 => match ctor_arg_tys Σenv I2 c0 with | Some tys0 => commute_branch_typed I1 C1 brs1 tys0 br0 | None => br0 end) brs2 0) c
        = Some (commute_branch_typed I1 C1 brs1 tys brI)).
    { unfold branch.
      apply (mapi_nth_error
               (f := fun c0 br0 => match ctor_arg_tys Σenv I2 c0 with
                                   | Some tys0 => commute_branch_typed I1 C1 brs1 tys0 br0
                                   | None => br0
                                   end)
               (xs := brs2) (i := 0) (n := c) (x := brI)) in HbI.
      simpl in HbI.
      rewrite Nat.add_0_l in HbI.
      unfold ctor_arg_tys in HΣI.
      unfold ctor_arg_tys.
      rewrite HΣI, Hctor.
      subst tys.
      exact HbI. }
    (* original steps to join *)
    set (inner := tCase I2 (tRoll I2 c params recs) C2 brs2).
    assert (Hinner_step : step inner (Cbn.apps brI (params ++ recs))).
    { subst inner. eapply step_case_roll; eauto. }
    set (join := tCase I1 (Cbn.apps brI (params ++ recs)) C1 brs1).
    assert (Horig_step : step (tCase I1 inner C1 brs1) join).
    { subst join. eapply step_case_scrut. exact Hinner_step. }
    pose proof (steps_step _ _ Horig_step) as Horig_steps.
    pose proof (steps_to_value_unique _ _ _ (proj1 Hterm) (proj2 Hterm) Horig_steps) as Hjoin_steps.
    set (Hjoin_term := (conj Hjoin_steps (proj2 Hterm)) : terminates_to join v).
    (* use branch lemma to transport termination from join to transformed branch application *)
    pose proof (proj2 (terminates_to_commute_branch_typed I1 C1 brs1 tys brI (params ++ recs) v Hargslen)) as Hjoin_to_app.
    pose proof (Hjoin_to_app Hjoin_term) as Happ_term.
    (* commuted term reduces in one step to that application *)
    set (trans := tCase I2 (tRoll I2 c params recs) C2 (mapi (fun c0 br0 => match ctor_arg_tys Σenv I2 c0 with | Some tys0 => commute_branch_typed I1 C1 brs1 tys0 br0 | None => br0 end) brs2 0)).
    assert (Htrans_step : step trans (Cbn.apps (commute_branch_typed I1 C1 brs1 tys brI) (params ++ recs))).
    { subst trans. eapply step_case_roll; eauto. }
    pose proof (steps_step _ _ Htrans_step) as Htrans_steps.
    split.
    + eapply steps_trans; [exact Htrans_steps|exact (proj1 Happ_term)].
    + exact (proj2 Happ_term).
  - (* backward: commuted -> original *)
    intros Δ σ v Hσ Hvσ Hterm.
    destruct t as [x|i|A1 B|A1 t1|t1 t2|A1 t1|I1|I1 c1 ps1 rs1|I1 scrut1 C1 brs1];
      simpl in *; try exact Hterm.
    destruct scrut1 as [x0|i0|A2 B2|A2 t2'|t2' u2|A2 t2'|I2|I2 c2 ps2 rs2|I2 scrut2 C2 brs2];
      simpl in *; try exact Hterm.
    destruct scrut2 as [xvar| | | | | | | | ]; try exact Hterm.
    assert (Hxlen : xvar < length σ).
    { rewrite (Ty.has_subst_length _ _ _ _ Hσ).
      inversion Hty; subst; try lia.
      inversion H4; subst; try lia.
      inversion H6; subst.
      eapply Ty.ctx_lookup_lt; eauto. }
    destruct (nth_error σ xvar) as [u|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
    inversion Hty; subst.
    inversion H4; subst.
    inversion H6; subst.
    pose proof (has_subst_lookup_tInd Σenv Δ σ Γ xvar I2 u Hσ H8 Hnth) as Hut.
    pose proof (Forall_nth_error _ _ _ Hvσ Hnth) as Hvalu.
    destruct (value_has_type_tInd_roll Σenv Δ u I2 Hvalu Hut)
      as (ΣI&ctor&c&params&recs&->&HΣI&Hctor&Hlenp&Hlenr).
    unfold ctor_arg_tys.
    rewrite HΣI, Hctor.
    set (tys := SP.ctor_param_tys ctor ++ repeat (tInd I2) (SP.ctor_rec_arity ctor)).
    assert (Hargslen : length (params ++ recs) = length tys).
    { subst tys. rewrite app_length, repeat_length. lia. }
    assert (HbrI : exists brI, branch brs2 c = Some brI).
    { inversion H4; subst.
      specialize (H12 c ctor Hctor) as (brI&Hb&HTybrI).
      exists brI. exact Hb. }
    destruct HbrI as [brI HbI].
    (* commuted term reduces to transformed branch application *)
    set (trans := tCase I2 (tRoll I2 c params recs) C2 (mapi (fun c0 br0 => match ctor_arg_tys Σenv I2 c0 with | Some tys0 => commute_branch_typed I1 C1 brs1 tys0 br0 | None => br0 end) brs2 0)).
    assert (Htrans_step : step trans (Cbn.apps (commute_branch_typed I1 C1 brs1 tys brI) (params ++ recs))).
    { subst trans. eapply step_case_roll; eauto.
      (* branch premise *)
      unfold branch.
      apply (mapi_nth_error
               (f := fun c0 br0 => match ctor_arg_tys Σenv I2 c0 with
                                   | Some tys0 => commute_branch_typed I1 C1 brs1 tys0 br0
                                   | None => br0
                                   end)
               (xs := brs2) (i := 0) (n := c) (x := brI)) in HbI.
      simpl in HbI.
      rewrite Nat.add_0_l in HbI.
      unfold ctor_arg_tys in HΣI.
      unfold ctor_arg_tys.
      rewrite HΣI, Hctor.
      subst tys.
      exact HbI. }
    pose proof (steps_step _ _ Htrans_step) as Htrans_steps.
    (* from commuted termination get termination of the transformed app *)
    pose proof (steps_to_value_unique _ _ _ (proj1 Hterm) (proj2 Hterm) Htrans_steps) as Happ_steps.
    set (Happ_term := (conj Happ_steps (proj2 Hterm)) : terminates_to (Cbn.apps (commute_branch_typed I1 C1 brs1 tys brI) (params ++ recs)) v).
    (* transport termination from transformed app to join *)
    pose proof (proj1 (terminates_to_commute_branch_typed I1 C1 brs1 tys brI (params ++ recs) v Hargslen)) as Happ_to_join.
    pose proof (Happ_to_join Happ_term) as Hjoin_term.
    (* original term steps to join *)
    set (inner := tCase I2 (tRoll I2 c params recs) C2 brs2).
    assert (Hinner_step : step inner (Cbn.apps brI (params ++ recs))).
    { subst inner. eapply step_case_roll; eauto. }
    set (join := tCase I1 (Cbn.apps brI (params ++ recs)) C1 brs1).
    assert (Horig_step : step (tCase I1 inner C1 brs1) join).
    { subst join. eapply step_case_scrut. exact Hinner_step. }
    pose proof (steps_step _ _ Horig_step) as Horig_steps.
    (* conclude: original terminates to v *)
    split.
    + eapply steps_trans; [exact Horig_steps|exact (proj1 Hjoin_term)].
    + exact (proj2 Hjoin_term).
Qed.

(** A reference-level cyclic-proof transform implemented by extract/re-read-off.

    This is *not* the final in-graph rewrite, but it gives a concrete function to
    target with equivalence-preservation theorems first.
*)
Definition commute_case_case_raw (Σenv : Ty.env) (t : tm) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv t).

Definition commute_case_case_builder (Σenv : Ty.env) (b : RO.builder) (root : nat) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv (EX.extract b root)).
