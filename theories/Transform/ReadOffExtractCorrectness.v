From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude gmap.

From Cyclic.Syntax Require Import Term.
From Cyclic.Transform Require Import ReadOff Extract.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Equiv Require Import CIUJudgement.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module RO := ReadOff.
Module EX := Extract.
Module Ty := Typing.Typing.

(**
  Read-off/extract correctness bridge.

  This file closes the loop needed by proof-level transforms.

  Target theorem (bridge):

    `extract_read_off_ciu : ciu_jTy Σ Γ t (extract_read_off t) A`

  We currently prove this via a stronger, syntactic round-trip lemma:

    `extract_read_off_id : extract_read_off t = t`.

  This is the main remaining isomorphism law for the raw pipeline.
*)

(** Build the extraction fix environment from a compilation back environment.

    This matches the intended correspondence:
    - entering a binder (`None :: ρ`) shifts indices
    - entering a fix (`Some target :: ρ`) both shifts and binds the target to 0
*)
Fixpoint fix_env_of (ρ : RO.back_env) : EX.fix_env :=
  match ρ with
  | [] => (∅ : EX.fix_env)
  | None :: ρ' => EX.env_shift (fix_env_of ρ')
  | Some target :: ρ' => <[target := 0]> (EX.env_shift (fix_env_of ρ'))
  end.

Lemma fix_env_of_nil : fix_env_of [] = (∅ : EX.fix_env).
Proof. reflexivity. Qed.

Lemma fix_env_of_cons_none (ρ : RO.back_env) :
  fix_env_of (None :: ρ) = EX.env_shift (fix_env_of ρ).
Proof. reflexivity. Qed.

Lemma fix_env_of_cons_some (v : nat) (ρ : RO.back_env) :
  fix_env_of (Some v :: ρ) = <[v := 0]> (EX.env_shift (fix_env_of ρ)).
Proof. reflexivity. Qed.

Fixpoint targets_of (ρ : RO.back_env) : list nat :=
  match ρ with
  | [] => []
  | None :: ρ' => targets_of ρ'
  | Some v :: ρ' => v :: targets_of ρ'
  end.

Definition nodup_targets (ρ : RO.back_env) : Prop := NoDup (targets_of ρ).

Lemma nodup_targets_tail (o : option nat) (ρ : RO.back_env) :
  nodup_targets (o :: ρ) -> nodup_targets ρ.
Proof.
  intro H.
  destruct o; simpl in *.
  - inversion H; subst; assumption.
  - exact H.
Qed.

Lemma fix_env_of_nth_some (ρ : RO.back_env) (x target : nat) :
  nodup_targets ρ ->
  nth_error ρ x = Some (Some target) ->
  fix_env_of ρ !! target = Some x.
Proof.
  revert x.
  induction ρ as [|o ρ IH]; intros [|x] Hnd H; simpl in *.
  - discriminate.
  - discriminate.
  - destruct o; simpl in H.
    + inversion H; subst.
      rewrite fix_env_of_cons_some.
      rewrite lookup_insert.
      reflexivity.
    + discriminate.
  - destruct o as [v|].
    + simpl in H.
      rewrite fix_env_of_cons_some.
      specialize (IH x (nodup_targets_tail _ _ Hnd) H).
      (* target comes from tail, so it cannot be v by NoDup *)
      assert (target <> v).
      { intro ->.
        (* v appears at head and also in tail at index x *)
        inversion Hnd as [|?? Hnotin]; subst.
        apply Hnotin.
        (* show v in targets_of ρ using nth_error hypothesis *)
        clear -H.
        revert ρ H.
        induction x as [|x IHx]; intros ρ H.
        - destruct ρ as [|o ρ']; simpl in H; try discriminate.
          destruct o; inversion H; subst; simpl; auto.
        - destruct ρ as [|o ρ']; simpl in H; try discriminate.
          destruct o; simpl.
          + right. eapply IHx. exact H.
          + eapply IHx. exact H.
      }
      rewrite lookup_insert_ne by exact H0.
      unfold EX.env_shift.
      rewrite lookup_fmap.
      rewrite IH.
      simpl.
      reflexivity.
    + (* None binder *)
      simpl in H.
      rewrite fix_env_of_cons_none.
      specialize (IH x (nodup_targets_tail _ _ Hnd) H).
      unfold EX.env_shift.
      rewrite lookup_fmap.
      rewrite IH.
      simpl.
      reflexivity.
Qed.

(** Term-level application spine (left-associated). *)
Fixpoint apps_tm (t : T.tm) (us : list T.tm) : T.tm :=
  match us with
  | [] => t
  | u :: us => apps_tm (T.tApp t u) us
  end.

Lemma app_view_correct (t : T.tm) :
  let '(h, args) := RO.app_view t in
  t = apps_tm h args.
Proof.
  induction t; simpl; try reflexivity.
  (* tApp case *)
  destruct (RO.app_view t1) as [h args] eqn:H.
  simpl.
  rewrite IHt1.
  (* show: apps_tm h (args ++ [t2]) = apps_tm (apps_tm h args) [t2] *)
  clear IHt1.
  revert h.
  induction args as [|a args IH]; intro h; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(**
  Main round-trip theorem.

  NOTE: This is still in progress. The intended proof is by induction on the fuel
  in `RO.compile_tm`, maintaining invariants relating:
  - the compilation back environment `ρ`
  - the extraction fix environment `fix_env_of ρ`
  - the fact that every `Some target` in `ρ` is a previously allocated vertex
    (so extraction introduces `fix` binders exactly at cycle targets)

  The only currently open sub-lemma above is the freshness/no-duplication fact
  needed to finish `fix_env_of_nth_some` cleanly.
*)
Theorem extract_read_off_id (t : T.tm) : EX.extract_read_off t = t.
Proof.
  unfold EX.extract_read_off, RO.read_off_raw, EX.extract.
  cbn.
  (* TODO: prove that extracting the compiled root yields `t`. *)
Admitted.

Theorem extract_read_off_ciu
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
  CIUJudgement.ciu_jTy Σenv Γ t (EX.extract_read_off t) A.
Proof.
  apply CIUJudgement.ciu_jTy_of_eq.
  apply extract_read_off_id.
Qed.
