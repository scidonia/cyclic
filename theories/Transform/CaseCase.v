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
Admitted.

Lemma terminates_to_steps_prefix (t u v : tm) :
  steps t u -> terminates_to t v -> terminates_to u v.
Proof.
Admitted.

Lemma steps_apps_congr (t t' : tm) (us : list tm) :
  steps t t' -> steps (Cbn.apps t us) (Cbn.apps t' us).
Proof.
Admitted.

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
Admitted.

Lemma steps_case_to_apps
    (I : nat) (scrut C : tm) (brs : list tm)
    (c : nat) (params recs : list tm) (br : tm) :
  steps scrut (tRoll I c params recs) ->
  branch brs c = Some br ->
  steps (tCase I scrut C brs) (Cbn.apps br (params ++ recs)).
Proof.
Admitted.


Lemma steps_to_value_unique (t u v : tm) :
  steps t v -> value v -> steps t u -> steps u v.
Proof.
Admitted.


Lemma shift1_tInd (I : nat) : shift1 (tInd I) = tInd I.
Proof.
  reflexivity.
Qed.

Lemma subst_list_tInd (σ : list tm) (I : nat) : Ty.subst_list σ (tInd I) = tInd I.
Proof.
  reflexivity.
Qed.

(** CIU preservation for the judgement-driven rewrite. *)
Theorem ciu_jTy_commute_case_case_once (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) :
  Ty.has_type Σenv Γ t A ->
  CIUJudgement.ciu_jTy Σenv Γ t (commute_case_case_once_typed Σenv t) A.
Proof.
Admitted.

(** A reference-level cyclic-proof transform implemented by extract/re-read-off.

    This is *not* the final in-graph rewrite, but it gives a concrete function to
    target with equivalence-preservation theorems first.
*)
Definition commute_case_case_raw (Σenv : Ty.env) (t : tm) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv t).

Definition commute_case_case_builder (Σenv : Ty.env) (b : RO.builder) (root : nat) : nat * RO.builder :=
  RO.read_off_raw (commute_case_case_once_typed Σenv (EX.extract b root)).
