From Stdlib Require Import List Arith Lia Utf8.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Equiv Require Import CIUNatObs.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.

(**
  Checklist example: [length (map f l)] observationally equals [length l].

  Key point: in our call-by-name semantics, constructors [tRoll] are values even
  when their arguments are not values. Thus [length l] evaluates to a chain of
  [succ] constructors carrying thunks, and for [length (map f l)] those thunks
  mention [map]. Syntactic value-observation is too intensional; instead we use
  the extensional Nat observation [terminates_to_nat] from [Equiv.CIUNatObs].
*)

(** * List-length observation (extensional) *)

Definition list_nil : tm := ListNat.nil.
Definition list_cons (x xs : tm) : tm := ListNat.cons x xs.

Inductive terminates_to_listlen (t : tm) : nat -> Prop :=
| tt_list_nil :
    steps t list_nil ->
    terminates_to_listlen t 0
| tt_list_cons x xs n :
    steps t (list_cons x xs) ->
    terminates_to_listlen xs n ->
    terminates_to_listlen t (S n).

Lemma terminates_to_listlen_nil_inv (t : tm) :
  terminates_to_listlen t 0 -> steps t list_nil.
Proof.
  intro H.
  inversion H; subst; eauto.
Qed.

Lemma terminates_to_listlen_cons_inv (t : tm) (n : nat) :
  terminates_to_listlen t (S n) ->
  exists x xs, steps t (list_cons x xs) /\ terminates_to_listlen xs n.
Proof.
  intro H.
  inversion H; subst.
  eauto.
Qed.

(** * Unfolded case forms for [map] and [length] *)

Definition map_case (f l : tm) : tm :=
  tCase 1 l ListNat.list_ty
    [
      list_nil;
      tLam Examples.nat_ty
        (tLam ListNat.list_ty
          (list_cons (tApp f (tVar 1)) (tApp (tApp ListNat.map f) (tVar 0))))
    ].

Definition length_case (l : tm) : tm :=
  tCase 1 l Examples.nat_ty
    [
      Examples.zero;
      tLam Examples.nat_ty
        (tLam ListNat.list_ty
          (Examples.succ (tApp ListNat.length (tVar 0))))
    ].

Lemma steps_map_to_case (f l : tm) :
  steps (tApp (tApp ListNat.map f) l) (map_case f l).
Proof.
  (* Unfold fix at the head, then beta-reduce twice. *)
  unfold ListNat.map, ListNat.map_body.
  cbn [map_case].
  (* steps: (map f) l  ->  ((unfold map) f) l *)
  eapply steps_trans.
  - (* unfold fix under two applications *)
    (* first move inside: tApp ListNat.map f *)
    eapply steps_trans.
    + (* unfold fix in function position *)
      apply Cbn.steps_app1.
      apply Cbn.steps_step.
      apply Cbn.step_fix.
    + (* beta: apply unfolded lambda to f *)
      apply Cbn.steps_step.
      apply Cbn.step_beta.
  - (* beta: apply resulting lambda to l *)
    apply Cbn.steps_step.
    apply Cbn.step_beta.
Qed.

Lemma steps_length_to_case (l : tm) :
  steps (tApp ListNat.length l) (length_case l).
Proof.
  unfold ListNat.length, ListNat.length_body.
  cbn [length_case].
  eapply steps_trans.
  - apply Cbn.steps_app1.
    apply Cbn.steps_step.
    apply Cbn.step_fix.
  - apply Cbn.steps_step.
    apply Cbn.step_beta.
Qed.

(** Beta-reduce a 2-argument branch application. *)
Lemma steps_apps_beta2
    (A B body u v : tm) :
  steps (tApp (tApp (tLam A (tLam B body)) u) v) (body.[u/].[v/]).
Proof.
  eapply Cbn.steps_trans.
  - (* contract the left β-redex under the outer application *)
    apply Cbn.steps_app1.
    apply Cbn.steps_step.
    apply Cbn.step_beta.
  - (* now contract the remaining β-redex *)
    apply Cbn.steps_step.
    apply Cbn.step_beta.
Qed.

(** * [map] preserves list-length observation *)

Lemma steps_map_nil (f l : tm) :
  steps l list_nil ->
  steps (tApp (tApp ListNat.map f) l) list_nil.
Proof.
  intro Hl.
  eapply Cbn.steps_trans.
  - apply steps_map_to_case.
  - (* case on nil *)
    eapply Cbn.steps_case_to_apps.
    + exact Hl.
    + reflexivity.
Qed.

Lemma steps_map_cons (f l x xs : tm) :
  steps l (list_cons x xs) ->
  steps (tApp (tApp ListNat.map f) l)
        (list_cons (tApp f x) (tApp (tApp ListNat.map f) xs)).
Proof.
  intro Hl.
  eapply Cbn.steps_trans.
  - apply steps_map_to_case.
  - (* case on cons *)
    eapply Cbn.steps_trans.
    + eapply Cbn.steps_case_to_apps.
      * exact Hl.
      * reflexivity.
    + (* reduce apps of the cons branch *)
      cbn.
      (* (\x. \xs. cons (f x) (map f xs)) x xs *)
      eapply Cbn.steps_trans.
      * apply steps_apps_beta2.
      * (* simplify the substitution result *)
        cbn.
        apply Cbn.rt_refl.
Qed.

Lemma terminates_to_listlen_map_fwd (f l : tm) (n : nat) :
  terminates_to_listlen l n ->
  terminates_to_listlen (tApp (tApp ListNat.map f) l) n.
Proof.
  revert l.
  induction n as [|n IH]; intros l Hlen.
  - apply tt_list_nil.
    apply steps_map_nil.
    apply terminates_to_listlen_nil_inv.
    exact Hlen.
  - destruct (terminates_to_listlen_cons_inv _ _ Hlen) as [x [xs [Hl Hxs]]].
    eapply tt_list_cons.
    + apply steps_map_cons. exact Hl.
    + apply IH. exact Hxs.
Qed.

Lemma steps_case_value_inv
    (I : nat) (scrut C v : tm) (brs : list tm) :
  value v ->
  steps (tCase I scrut C brs) v ->
  exists c args br,
    steps scrut (tRoll I c args)
    /\ branch brs c = Some br
    /\ steps (apps br args) v.
Proof.
  intros Hv Hsteps.
  revert scrut C brs.
  induction Hsteps as [t u Hst|t|t u w _ Htu IHu _ Huw IHw];
    intros scrut C0 brs0.
  - (* rt_step *)
    inversion Hst; subst; try solve [inversion Hv].
    exists c, args, br.
    split.
    + apply Cbn.rt_refl.
    + split; [exact H|apply Cbn.rt_refl].
  - (* rt_refl *)
    (* impossible: a [tCase] is never a value *)
    inversion Hv.
  - (* rt_trans *)
    destruct (Cbn.steps_decomp _ _ Htu) as [->|[t1 [Hstep Hrest]]].
    + (* t = u; so just use IHw *)
      exact (IHw _ _ _ Hv Huw).
    + (* first step from the case *)
      inversion Hstep; subst.
      * (* scrutinee step: keep chasing *)
        specialize (IHw _ _ _ Hv Huw) as [c [args [br [Hscrut [Hbr Happs]]]]].
        exists c, args, br.
        split.
        { eapply Cbn.steps_trans.
          - apply Cbn.steps_step. exact H0.
          - exact Hscrut. }
        split; [exact Hbr|exact Happs].
      * (* roll step *)
        exists c, args, br.
        split.
        { apply Cbn.rt_refl. }
        split; [exact H|].
        (* now we already have one roll step; continue with rest *)
        exact Huw.
Qed.

Lemma steps_map_nil_inv (f l : tm) :
  steps (tApp (tApp ListNat.map f) l) list_nil ->
  steps l list_nil.
Proof.
  intro Hmap.
  (* Move to the unfolded case form. *)
  pose proof (steps_map_to_case f l) as Hto.
  have Hcase : steps (map_case f l) list_nil.
  { eapply Cbn.steps_to_value_unique; [exact Hmap| |exact Hto].
    unfold list_nil. apply Cbn.v_roll. }
  (* Invert the case reduction. *)
  destruct (steps_case_value_inv 1 l ListNat.list_ty list_nil _ (Cbn.v_roll _ _ _) Hcase)
    as [c [args [br [Hl [Hbr Happs]]]]].
  cbn in Hbr.
  destruct c as [|c]; [|discriminate].
  destruct args as [|? ?]; [|discriminate].
  simpl in Hl.
  (* scrutinee must reduce to nil *)
  exact Hl.
Qed.

Lemma steps_map_cons_inv (f l y ys : tm) :
  steps (tApp (tApp ListNat.map f) l) (list_cons y ys) ->
  exists x xs,
    steps l (list_cons x xs)
    /\ y = tApp f x
    /\ ys = tApp (tApp ListNat.map f) xs.
Proof.
  intro Hmap.
  pose proof (steps_map_to_case f l) as Hto.
  have Hcase : steps (map_case f l) (list_cons y ys).
  { eapply Cbn.steps_to_value_unique; [exact Hmap| |exact Hto].
    apply Cbn.v_roll. }
  destruct (steps_case_value_inv 1 l ListNat.list_ty (list_cons y ys) _ (Cbn.v_roll _ _ _) Hcase)
    as [c [args [br [Hl [Hbr Happs]]]]].
  cbn in Hbr.
  destruct c as [|c].
  - (* nil branch cannot produce a cons *)
    exfalso.
    (* apps of the nil branch is nil (a different constructor) *)
    assert (Happs' : steps list_nil (list_cons y ys)).
    { eapply Cbn.steps_trans.
      - exact Happs.
      - apply Cbn.rt_refl. }
    (* impossible since values do not step to other values *)
    eapply Cbn.value_no_step.
    + unfold list_nil. apply Cbn.v_roll.
    + destruct (Cbn.steps_decomp _ _ Happs') as [Heq|[t1 [Hst _]]].
      * rewrite Heq in *. inversion 1.
      * exact Hst.
  - (* cons branch *)
    destruct c as [|c]; [|discriminate].
    destruct args as [|x [|xs args]]; try discriminate.
    destruct args; [|discriminate].
    (* identify the branch and normalize its application *)
    subst br.
    cbn in Happs.
    (* expected cons value *)
    set (expected := list_cons (tApp f x) (tApp (tApp ListNat.map f) xs)).
    have Hexp : steps (apps (tLam Examples.nat_ty
                              (tLam ListNat.list_ty
                                (list_cons (tApp f (tVar 1))
                                          (tApp (tApp ListNat.map f) (tVar 0))))) [x; xs]) expected.
    { cbn [apps expected].
      eapply Cbn.steps_trans.
      - apply steps_apps_beta2.
      - cbn. apply Cbn.rt_refl. }
    have Heqv : expected = (list_cons y ys).
    { (* both are values reachable from the same term *)
      assert (Hexp' : steps (apps (tLam Examples.nat_ty
                                    (tLam ListNat.list_ty
                                      (list_cons (tApp f (tVar 1))
                                                (tApp (tApp ListNat.map f) (tVar 0))))) [x; xs]) (list_cons y ys)).
      { exact Happs. }
      (* uniqueness of evaluation to a value *)
      have : steps expected (list_cons y ys).
      { eapply Cbn.steps_to_value_unique; [exact Hexp'| |exact Hexp].
        unfold expected. apply Cbn.v_roll. }
      (* since expected is a value, no steps unless equal *)
      destruct (Cbn.steps_decomp _ _ this) as [Heq|[t1 [Hst _]]].
      - exact Heq.
      - exfalso.
        eapply Cbn.value_no_step; [unfold expected; apply Cbn.v_roll|exact Hst]. }
    unfold expected in Heqv.
    inversion Heqv; subst.
    exists x, xs.
    repeat split; eauto.
Qed.

Lemma terminates_to_listlen_map_bwd (f l : tm) (n : nat) :
  terminates_to_listlen (tApp (tApp ListNat.map f) l) n ->
  terminates_to_listlen l n.
Proof.
  revert l.
  induction n as [|n IH]; intros l Hlen.
  - apply tt_list_nil.
    apply steps_map_nil_inv with (f := f).
    apply terminates_to_listlen_nil_inv.
    exact Hlen.
  - destruct (terminates_to_listlen_cons_inv _ _ Hlen) as [y [ys [Hmap Hys]]].
    destruct (steps_map_cons_inv f l y ys Hmap) as [x [xs [Hl [-> ->]]]].
    eapply tt_list_cons.
    + exact Hl.
    + apply IH.
      exact Hys.
Qed.

Lemma terminates_to_listlen_map_iff (f l : tm) (n : nat) :
  terminates_to_listlen (tApp (tApp ListNat.map f) l) n <-> terminates_to_listlen l n.
Proof.
  split.
  - apply terminates_to_listlen_map_bwd.
  - apply terminates_to_listlen_map_fwd.
Qed.

(** * [length] computes the list-length observation *)

Lemma steps_length_nil (l : tm) :
  steps l list_nil ->
  steps (tApp ListNat.length l) Examples.zero.
Proof.
  intro Hl.
  eapply Cbn.steps_trans.
  - apply steps_length_to_case.
  - eapply Cbn.steps_case_to_apps.
    + exact Hl.
    + reflexivity.
Qed.

Lemma steps_length_cons (l x xs : tm) :
  steps l (list_cons x xs) ->
  steps (tApp ListNat.length l) (Examples.succ (tApp ListNat.length xs)).
Proof.
  intro Hl.
  eapply Cbn.steps_trans.
  - apply steps_length_to_case.
  - eapply Cbn.steps_trans.
    + eapply Cbn.steps_case_to_apps.
      * exact Hl.
      * reflexivity.
    + cbn.
      (* (\x. \xs. succ (length xs)) x xs *)
      eapply Cbn.steps_trans.
      * apply steps_apps_beta2.
      * cbn. apply Cbn.rt_refl.
Qed.

Lemma terminates_to_nat_length_of_listlen (l : tm) (n : nat) :
  terminates_to_listlen l n ->
  terminates_to_nat (tApp ListNat.length l) n.
Proof.
  revert l.
  induction n as [|n IH]; intros l Hlen.
  - apply tt_nat_zero.
    apply steps_length_nil.
    apply terminates_to_listlen_nil_inv.
    exact Hlen.
  - destruct (terminates_to_listlen_cons_inv _ _ Hlen) as [x [xs [Hl Hxs]]].
    eapply tt_nat_succ with (t' := tApp ListNat.length xs).
    + apply steps_length_cons with (x := x) (xs := xs).
      exact Hl.
    + apply IH.
      exact Hxs.
Qed.

Lemma terminates_to_listlen_of_nat_length (l : tm) (n : nat) :
  terminates_to_nat (tApp ListNat.length l) n ->
  terminates_to_listlen l n.
Proof.
  revert l.
  induction n as [|n IH]; intros l Hnat.
  - (* length l observes 0 => l is nil *)
    apply tt_list_nil.
    (* move to case form *)
    pose proof (steps_length_to_case l) as Hto.
    have Hcase : steps (length_case l) Examples.zero.
    { eapply Cbn.steps_to_value_unique; [| |exact Hto].
      - apply (terminates_to_nat_zero_inv _ Hnat).
      - unfold Examples.zero. apply Cbn.v_roll. }
    destruct (steps_case_value_inv 1 l Examples.nat_ty Examples.zero _ (Cbn.v_roll _ _ _) Hcase)
      as [c [args [br [Hl [Hbr Happs]]]]].
    cbn in Hbr.
    destruct c as [|c]; [|discriminate].
    destruct args as [|? ?]; [|discriminate].
    exact Hl.
  - (* successor observation *)
    destruct (terminates_to_nat_succ_inv _ _ Hnat) as [t' [Hstep Hnat']].
    eapply tt_list_cons.
    + (* show l reduces to a cons *)
      pose proof (steps_length_to_case l) as Hto.
      have Hcase : steps (length_case l) (Examples.succ t').
      { eapply Cbn.steps_to_value_unique; [| |exact Hto].
        - exact Hstep.
        - apply Cbn.v_roll. }
      destruct (steps_case_value_inv 1 l Examples.nat_ty (Examples.succ t') _ (Cbn.v_roll _ _ _) Hcase)
        as [c [args [br [Hl [Hbr Happs]]]]].
      cbn in Hbr.
      destruct c as [|c].
      * discriminate.
      * destruct c as [|c]; [|discriminate].
        destruct args as [|x [|xs args]]; try discriminate.
        destruct args; [|discriminate].
        subst br.
        (* normalize the succ-branch application *)
        set (expected := Examples.succ (tApp ListNat.length xs)).
        have Hexp : steps (apps (tLam Examples.nat_ty
                                  (tLam ListNat.list_ty
                                    (Examples.succ (tApp ListNat.length (tVar 0))))) [x; xs]) expected.
        { cbn [apps expected].
          eapply Cbn.steps_trans.
          - apply steps_apps_beta2.
          - cbn. apply Cbn.rt_refl. }
        have Heqv : expected = Examples.succ t'.
        { have : steps expected (Examples.succ t').
          { eapply Cbn.steps_to_value_unique; [exact Happs| |exact Hexp].
            unfold expected. apply Cbn.v_roll. }
          destruct (Cbn.steps_decomp _ _ this) as [Heq|[t1 [Hst _]]].
          - exact Heq.
          - exfalso.
            eapply Cbn.value_no_step; [unfold expected; apply Cbn.v_roll|exact Hst]. }
        unfold expected in Heqv.
        inversion Heqv; subst.
        exact Hl.
    + (* now use IH on the thunk, after rewriting t' = length xs *)
      (* from the equality established above, t' is [tApp length xs] *)
      (* reconstruct xs by repeating the inversion steps above *)
      pose proof (steps_length_to_case l) as Hto.
      have Hcase : steps (length_case l) (Examples.succ t').
      { eapply Cbn.steps_to_value_unique; [| |exact Hto].
        - exact Hstep.
        - apply Cbn.v_roll. }
      destruct (steps_case_value_inv 1 l Examples.nat_ty (Examples.succ t') _ (Cbn.v_roll _ _ _) Hcase)
        as [c [args [br [_Hl [Hbr Happs]]]]].
      cbn in Hbr.
      destruct c as [|c]; [discriminate|].
      destruct c as [|c]; [|discriminate].
      destruct args as [|x [|xs args]]; try discriminate.
      destruct args; [|discriminate].
      subst br.
      (* as above, establish that [t'] is [tApp length xs] *)
      set (expected := Examples.succ (tApp ListNat.length xs)).
      have Hexp : steps (apps (tLam Examples.nat_ty
                                (tLam ListNat.list_ty
                                  (Examples.succ (tApp ListNat.length (tVar 0))))) [x; xs]) expected.
      { cbn [apps expected].
        eapply Cbn.steps_trans.
        - apply steps_apps_beta2.
        - cbn. apply Cbn.rt_refl. }
      have Heqv : expected = Examples.succ t'.
      { have : steps expected (Examples.succ t').
        { eapply Cbn.steps_to_value_unique; [exact Happs| |exact Hexp].
          unfold expected. apply Cbn.v_roll. }
        destruct (Cbn.steps_decomp _ _ this) as [Heq|[t1 [Hst _]]].
        - exact Heq.
        - exfalso.
          eapply Cbn.value_no_step; [unfold expected; apply Cbn.v_roll|exact Hst]. }
      unfold expected in Heqv.
      inversion Heqv; subst.
      apply IH.
      exact Hnat'.
Qed.

Lemma terminates_to_nat_length_iff_listlen (l : tm) (n : nat) :
  terminates_to_nat (tApp ListNat.length l) n <-> terminates_to_listlen l n.
Proof.
  split.
  - apply terminates_to_listlen_of_nat_length.
  - apply terminates_to_nat_length_of_listlen.
Qed.

(** * Final checklist lemma *)

Lemma nat_obs_rel_length_map (f l : tm) :
  nat_obs_rel (tApp ListNat.length (tApp (tApp ListNat.map f) l)) (tApp ListNat.length l).
Proof.
  intro n.
  (* shuttle through list-length observation *)
  rewrite (terminates_to_nat_length_iff_listlen (l := (tApp (tApp ListNat.map f) l)) (n := n)).
  rewrite (terminates_to_listlen_map_iff f l n).
  rewrite <- (terminates_to_nat_length_iff_listlen (l := l) (n := n)).
  tauto.
Qed.

(** A CIU wrapper in the standard judgement-level style. *)

Definition Σ_listnat : Ty.env := [Examples.Nat_sig; ListNat.List_sig].
Definition Γ_listnat : Ty.ctx := [ListNat.list_ty; ListNat.nat2nat].

Definition t_len_map : tm :=
  tApp ListNat.length (tApp (tApp ListNat.map (tVar 1)) (tVar 0)).

Definition t_len : tm := tApp ListNat.length (tVar 0).

Lemma ciu_jNatObs_length_map :
  CIUNatObs.ciu_jNatObs Σ_listnat Γ_listnat t_len_map t_len.
Proof.
  intros Δ σ Hσ Hvσ n.
  (* unfold the list-substitution (Γ has exactly two variables) *)
  cbn [t_len_map t_len].
  unfold Ty.subst_list, Typing.Typing.subst_list, Ty.subst_sub, Typing.Typing.subst_sub.
  cbn [Typing.Typing.sub_fun].
  destruct σ as [|l [|f σ]]; simpl in *.
  - inversion Hσ.
  - inversion Hσ.
  - (* σ = l :: f :: [] by has_subst_length *)
    assert (Hlen : length σ = 2) by (apply Ty.has_subst_length in Hσ; simpl in Hσ; lia).
    destruct σ; [|discriminate].
    (* apply the closed Nat observational equivalence lemma *)
    specialize (nat_obs_rel_length_map f l n).
    cbn.
    exact (nat_obs_rel_length_map f l n).
Qed.
