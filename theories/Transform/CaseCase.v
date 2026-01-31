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
          (* For now, simplified: just param types.
             A full implementation would need to handle indexed rec occurrences. *)
          Some (SP.ctor_param_tys ctor)
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
  | [] =>
      (* D is a dependent motive (a binder), so preserve its bound scrutinee
         at index 0 by shifting under cutoff 1. *)
      tCase J br_acc (shift k 1 D) (map (shift k 0) brsJ)
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

(** Motive propagation: when we know the scrutinee is a constructor,
    we can propagate that information into the dependent motive.
    
    Transform: case (roll I c args) C brs
            -> case (roll I c args) C[roll I c args/x] brs
    
    This is semantically a no-op (the substitution was going to happen anyway
    when the case reduces), but it can enable further optimizations by
    making the motive more concrete.
*)
Definition propagate_motive_once (t : tm) : tm :=
  match t with
  | tCase ind (tRoll ind' c args as scrut) C brs =>
      if Nat.eqb ind ind' then
        tCase ind scrut (subst0 scrut C) brs
      else t
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
  exists c args br,
    steps scrut (tRoll I c args)
    /\ branch brs c = Some br
    /\ terminates_to (subst0 (tRoll I c args) (Cbn.apps br args)) v.
Proof.
  intros [Hcase Hv].

  assert (Hdecomp : forall (t0 t : tm),
             steps t0 t ->
             forall (scrut0 : tm),
               t0 = tCase I scrut0 C brs ->
               (exists scrut1,
                   steps scrut0 scrut1 /\ t = tCase I scrut1 C brs)
               \/
               (exists c args br,
                   steps scrut0 (tRoll I c args)
                   /\ branch brs c = Some br
                   /\ steps (subst0 (tRoll I c args) (Cbn.apps br args)) t)).
  {
    intros t0 t Hsteps0.
    induction Hsteps0; intros scrut0 ->.
    - (* rt_step *)
      inversion H; subst.
      + left.
        eexists.
        split.
        * eapply steps_step; eauto.
        * reflexivity.
      + right.
        do 3 eexists.
        split.
        * apply rt_refl.
        * split; [eauto|].
          apply rt_refl.
    - (* rt_refl *)
      left.
      exists scrut0.
      split; [apply rt_refl|reflexivity].
    - (* rt_trans *)
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
          destruct Hr' as (c & args & br & Hscrut1roll & Hbr & Happs).
          exists c, args, br.
          split; [eapply steps_trans; eauto|].
          split; [exact Hbr|exact Happs].
      + right.
        destruct Hr as (c & args & br & Hscrutroll & Hbr & Happs).
        exists c, args, br.
        split; [exact Hscrutroll|].
        split; [exact Hbr|].
        eapply steps_trans; eauto.
  }

  specialize (Hdecomp (tCase I scrut C brs) v Hcase scrut eq_refl).
  destruct Hdecomp as [Hl|Hr].
  - destruct Hl as [scrut1 [_ ->]].
    exfalso. inversion Hv.
  - destruct Hr as (c & args & br & Hscrutroll & Hbr & Happs).
    exists c, args, br.
    split; [exact Hscrutroll|].
    split; [exact Hbr|].
    split; [exact Happs|exact Hv].
Qed.

(** Motive propagation is semantically a no-op.

    Our call-by-name semantics does not inspect the case motive at runtime, so
    changing it does not affect termination-to-value observations.
*)
Lemma propagate_motive_preserves_terminates_to :
  forall I c args C brs v,
    terminates_to (tCase I (tRoll I c args) (subst0 (tRoll I c args) C) brs) v
    <->
    terminates_to (tCase I (tRoll I c args) C brs) v.
Proof.
  intros I c args C brs v.
  split; intro Hterm.
  - destruct (terminates_to_case_inv I (tRoll I c args) (subst0 (tRoll I c args) C) brs v Hterm)
      as (c' & args' & br & Hscrut & Hbr & Happs).
    destruct Happs as [Happs_steps Hv].
    split.
    + eapply steps_trans.
      * eapply steps_case_to_apps; eauto.
      * exact Happs_steps.
    + exact Hv.
  - destruct (terminates_to_case_inv I (tRoll I c args) C brs v Hterm)
      as (c' & args' & br & Hscrut & Hbr & Happs).
    destruct Happs as [Happs_steps Hv].
    split.
    + eapply steps_trans.
      * eapply steps_case_to_apps; eauto.
      * exact Happs_steps.
    + exact Hv.
Qed.

Lemma terminates_to_steps_prefix (t u v : tm) :
  steps t u -> terminates_to t v -> terminates_to u v.
Proof.
  exact (Cbn.terminates_to_steps_prefix t u v).
Qed.

Lemma steps_apps_congr (t t' : tm) (us : list tm) :
  steps t t' -> steps (Cbn.apps t us) (Cbn.apps t' us).
Proof.
  exact (Cbn.steps_apps_congr t t' us).
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
  unfold shift, rename.
  rewrite rename_subst.
  assert (Hxi : shift_sub 0 0 = fun x => x).
  { apply functional_extensionality; intro x.
    unfold shift_sub.
    destruct (x <? 0) eqn:Hx.
    - apply Nat.ltb_lt in Hx. lia.
    - lia. }
  rewrite Hxi.
  assert (Hren : ren (fun x => x) = ids).
  { apply functional_extensionality; intro x.
    reflexivity. }
  rewrite Hren.
  unfold ids.
  exact (subst_id t).
Qed.

Lemma shift0_id_cutoff (c : nat) (t : tm) : shift 0 c t = t.
Proof.
  unfold shift, rename.
  rewrite rename_subst.
  assert (Hxi : shift_sub 0 c = fun x => x).
  { apply functional_extensionality; intro x.
    unfold shift_sub.
    destruct (x <? c) eqn:Hx; lia. }
  rewrite Hxi.
  assert (Hren : ren (fun x => x) = ids).
  { apply functional_extensionality; intro x.
    reflexivity. }
  rewrite Hren.
  unfold ids.
  exact (subst_id t).
Qed.

Lemma map_shift0_id (ts : list tm) : map (shift 0 0) ts = ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - reflexivity.
  - rewrite shift0_id. now rewrite IH.
Qed.

Fixpoint plug_sub (k : nat) (u : tm) : var -> tm :=
  match k with
  | 0 => u .: ids
  | S k => up (plug_sub k u)
  end.

Lemma shift_sub_0 (d x : nat) : shift_sub d 0 x = x + d.
Proof.
  unfold shift_sub.
  destruct (x <? 0) eqn:Hx.
  - apply Nat.ltb_lt in Hx. lia.
  - lia.
Qed.

Lemma plug_sub_on_shift (k : nat) (u : tm) :
  forall x, plug_sub k u (x + S k) = tVar (x + k).
Proof.
  induction k as [|k IH]; intros x; cbn [plug_sub].
  - replace (x + 1) with (S x) by lia.
    cbn.
    unfold ids, Autosubst_Classes.ids.
    unfold Term.Syntax.Ids_tm.
    now rewrite Nat.add_0_r.
  - replace (x + S (S k)) with (S (x + S k)) by lia.
    unfold up, Autosubst_Classes.up.
    cbn.
    rewrite IH.
    asimpl.
    replace (S (x + k)) with (x + S k) by lia.
    reflexivity.
Qed.

Lemma shift_plug_sub (k : nat) (u t : tm) :
  (shift (S k) 0 t).[plug_sub k u] = shift k 0 t.
Proof.
  unfold shift, rename.
  repeat rewrite rename_subst.
  rewrite subst_comp.
  assert (Hσ : ren (shift_sub (S k) 0) >> plug_sub k u = ren (shift_sub k 0)).
  { apply functional_extensionality; intro x.
    unfold funcomp.
    cbn [ren].
    asimpl.
    replace (S (x + k)) with (x + S k) by lia.
    rewrite plug_sub_on_shift.
    unfold ids, Autosubst_Classes.ids.
    unfold Term.Syntax.Ids_tm.
    reflexivity. }
  rewrite Hσ.
  reflexivity.
Qed.

(* Variant used for dependent case motives: shift under cutoff 1, then substitute
   under the binder (`up`). *)
Lemma shift_plug_sub_cutoff1 (k : nat) (u t : tm) :
  (shift (S k) 1 t).[up (plug_sub k u)] = shift k 1 t.
Proof.
  unfold shift, rename.
  repeat rewrite rename_subst.
  rewrite subst_comp.
  assert (Hσ : ren (shift_sub (S k) 1) >> up (plug_sub k u) = ren (shift_sub k 1)).
  { apply functional_extensionality; intro x.
    unfold funcomp.
    cbn [ren].
    asimpl.
    destruct x as [|x].
    - (* x = 0 *)
      cbn [shift_sub].
      unfold up, Autosubst_Classes.up.
      cbn.
      reflexivity.
    - (* x = S x *)
      cbn [shift_sub].
      replace (S x <? 1) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (S x + S k) with (S (x + S k)) by lia.
      unfold up, Autosubst_Classes.up.
      cbn.
      rewrite plug_sub_on_shift.
      cbn [rename].
      reflexivity. }
  rewrite Hσ.
  reflexivity.
Qed.

Lemma map_shift_plug_sub (k : nat) (u : tm) (ts : list tm) :
  (map (shift (S k) 0) ts)..[plug_sub k u] = map (shift k 0) ts.
Proof.
  induction ts as [|t ts IH]; cbn.
  - reflexivity.
  - asimpl.
    rewrite shift_plug_sub.
    f_equal.
    exact IH.
Qed.

Lemma shift1_subst_up (t : tm) (σ : var -> tm) :
  (shift1 t).[up σ] = shift1 (t.[σ]).
Proof.
  unfold shift1, shift, rename.
  repeat rewrite rename_subst.
  repeat rewrite subst_comp.
  assert (Hσ : ren (shift_sub 1 0) >> up σ = σ >> ren (shift_sub 1 0)).
  { apply functional_extensionality; intro x.
    unfold funcomp.
    cbn [ren].
    asimpl.
    (* up σ (S x) = (σ x).[ren (shift_sub 1 0)] *)
    unfold up, Autosubst_Classes.up.
    cbn.
    rewrite rename_subst.
    assert (Hxi : shift_sub 1 0 = (+1)).
    { apply functional_extensionality; intro y.
      unfold shift_sub.
      destruct (y <? 0) eqn:Hy.
      - apply Nat.ltb_lt in Hy. lia.
      - rewrite Nat.add_1_r.
        reflexivity. }
    rewrite Hxi.
    reflexivity. }
  rewrite Hσ.
  reflexivity.
Qed.

Lemma commute_branch_typed_rec_plug_sub
    (k : nat) (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br_acc u : tm) :
  (commute_branch_typed_rec (S k) J D brsJ argsTys br_acc).[plug_sub k u]
  = commute_branch_typed_rec k J D brsJ argsTys (br_acc.[plug_sub k u]).
Proof.
  revert k br_acc.
  induction argsTys as [|A argsTys IH]; intros k br_acc; cbn [commute_branch_typed_rec].
  - asimpl.
    f_equal.
    all: try reflexivity.
    all: try (apply shift_plug_sub_cutoff1).
    all: try (symmetry; apply shift_plug_sub_cutoff1).
    all: try apply map_shift_plug_sub.
  - asimpl.
    f_equal.
    + apply shift_plug_sub.
    + (* Put the substitution in `plug_sub (S k) u` form so IH matches. *)
      replace (up (plug_sub k u)) with (plug_sub (S k) u) by reflexivity.
      rewrite (IH (S k) (tApp (shift1 br_acc) (tVar 0))).
      f_equal.
      cbn.
      rewrite shift1_subst_up.
      reflexivity.
Qed.

Lemma subst0_commute_branch_typed_rec
    (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br_acc u : tm) :
  subst0 u
      (commute_branch_typed_rec 1 J D brsJ argsTys (tApp (shift1 br_acc) (tVar 0)))
  = commute_branch_typed_rec 0 J D brsJ argsTys (tApp br_acc u).
Proof.
  unfold subst0.
  (* instantiate commute_branch_typed_rec_plug_sub at k=0 *)
  pose proof (commute_branch_typed_rec_plug_sub 0 J D brsJ argsTys (tApp (shift1 br_acc) (tVar 0)) u) as H.
  cbn [plug_sub] in H.
  exact H.
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
    rewrite (shift0_id_cutoff 1 D).
    rewrite map_shift0_id.
    apply rt_refl.
  - destruct args as [|u us]; simpl in Hlen; [discriminate|].
    inversion Hlen as [Hlen'].
    cbn [commute_branch_typed_rec].
    eapply steps_trans.
    + apply steps_beta_apps.
    + cbn [shift1].
      asimpl.
      rewrite (subst0_commute_branch_typed_rec J D brsJ argsTys br_acc u).
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
    (c : nat) (args : list tm) (br : tm) :
  steps scrut (tRoll I c args) ->
  branch brs c = Some br ->
  steps (tCase I scrut C brs) (subst0 (tRoll I c args) (Cbn.apps br args)).
Proof.
  intros Hscrut Hbr.
  eapply Cbn.steps_case_to_apps; eauto.
Qed.


Lemma steps_to_value_unique (t u v : tm) :
  steps t v -> value v -> steps t u -> steps u v.
Proof.
  intros Htv Hv Htu.
  eapply Cbn.steps_to_value_unique; eauto.
Qed.


Lemma shift1_tInd (I : nat) : shift1 (tInd I []) = tInd I [].
Proof.
  reflexivity.
Qed.

Lemma subst_list_tInd (σ : list tm) (I : nat) : Ty.subst_list σ (tInd I []) = tInd I [].
Proof.
  reflexivity.
Qed.

Lemma steps_from_value_eq (v t : tm) :
  value v -> steps v t -> t = v.
Proof.
  intros Hv Hsteps.
  revert Hv.
  induction Hsteps; intros Hv.
  - (* rt_step *)
    exfalso. eapply value_no_step; eauto.
  - (* rt_refl *)
    reflexivity.
  - (* rt_trans *)
    specialize (IHHsteps1 Hv).
    subst.
    apply IHHsteps2.
    exact Hv.
Qed.

Lemma shift1_inj_tInd (t : tm) (I : nat) :
  shift1 t = tInd I [] -> t = tInd I [].
Proof.
  destruct t; cbn [shift1 shift]; intro H; try discriminate.
  (* t = tInd _ args *)
  match goal with
  | args : list tm |- _ => destruct args as [|a args]
  end.
  - inversion H; subst. reflexivity.
  - discriminate.
Qed.

Lemma subst_list_var_of_nth (σ : list tm) (x : nat) (u : tm) :
  nth_error σ x = Some u ->
  Ty.subst_list σ (tVar x) = u.
Proof.
  intro Hx.
  unfold Ty.subst_list, Typing.Typing.subst_list.
  unfold Ty.subst_sub, Typing.Typing.subst_sub, Typing.Typing.sub_fun.
  cbn.
  rewrite Hx.
  reflexivity.
Qed.

Lemma has_subst_nth_tInd
    (Σenv : Ty.env) (Δ : Ty.ctx) (σ : list tm) (Γ : Ty.ctx) (x I : nat) :
  Ty.has_subst Σenv Δ σ Γ ->
  Ty.ctx_lookup Γ x = Some (tInd I []) ->
  exists u,
    nth_error σ x = Some u /\ Ty.has_type Σenv Δ u (tInd I []).
Proof.
  intro Hs.
  revert x I.
  induction Hs as [|Γ0 A0 σ0 u0 Hs IH Htyu]; intros x I Hlookup.
  - cbn [Ty.ctx_lookup] in Hlookup. discriminate.
  - destruct x as [|x].
    + cbn [Ty.ctx_lookup] in Hlookup.
      inversion Hlookup as [Hshift].
      apply shift1_inj_tInd in Hshift.
      subst A0.
      exists u0.
      split; [reflexivity|].
      cbn in Htyu.
      exact Htyu.
    + cbn [Ty.ctx_lookup] in Hlookup.
      destruct (Ty.ctx_lookup Γ0 x) as [T|] eqn:HT; cbn in Hlookup; try discriminate.
      inversion Hlookup as [Hshift]; subst.
      apply shift1_inj_tInd in Hshift.
      subst T.
      destruct (IH x I HT) as (u & Hnth & Hty).
      exists u.
      split; [exact Hnth|exact Hty].
Qed.

Lemma value_has_type_tInd_inv
    (Σenv : Ty.env) (Γ : Ty.ctx) (v : tm) (I : nat) :
  value v -> Ty.has_type Σenv Γ v (tInd I []) ->
  exists ΣI ctor c args params recs,
    v = tRoll I c args
    /\ SP.lookup_ind Σenv I = Some ΣI
    /\ SP.lookup_ctor ΣI c = Some ctor
    /\ Ty.split_at (SP.ctor_param_arity ctor) args = (params, recs)
    /\ Forall2 (Ty.has_type Σenv Γ) params (SP.ctor_param_tys ctor)
    /\ Forall (fun r => Ty.has_type Σenv Γ r (tInd I [])) recs
    /\ length recs = SP.ctor_rec_arity ctor.
Proof.
  intros Hv Hty.
  inversion Hv; subst.
  - inversion Hty; subst; discriminate.
  - inversion Hty; subst.
    exists ΣI, ctor, c, args, params, recs.
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
  rewrite shift0_id.
  rewrite shift0_id.
  reflexivity.
Qed.


Lemma subst_list_commute_branch_typed
    (σ : list tm)
    (J : nat) (D : tm) (brsJ : list tm) (argsTys : list tm) (br : tm) :
  Ty.subst_list σ (commute_branch_typed J D brsJ argsTys br) =
  commute_branch_typed J (Ty.subst_list σ D) (map (Ty.subst_list σ) brsJ) (map (Ty.subst_list σ) argsTys) (Ty.subst_list σ br).
Admitted.

(** CIU preservation for the judgement-driven rewrite. *)
Theorem ciu_jTy_commute_case_case_once (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  Ty.has_type Σenv Γ t A ->
  CIUJudgement.ciu_jTy Σenv Γ t (commute_case_case_once_typed Σenv t) A.
Admitted.


