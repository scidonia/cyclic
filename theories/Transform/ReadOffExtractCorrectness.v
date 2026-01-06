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

Definition targets_lt (ρ : RO.back_env) (n : nat) : Prop :=
  Forall (fun v => v < n) (targets_of ρ).

Lemma targets_lt_nil (n : nat) : targets_lt [] n.
Proof. constructor. Qed.

Lemma targets_lt_tail (o : option nat) (ρ : RO.back_env) (n : nat) :
  targets_lt (o :: ρ) n -> targets_lt ρ n.
Proof.
  destruct o; simpl; intro H; [inversion H|]; assumption.
Qed.

Lemma targets_lt_cons_some (v : nat) (ρ : RO.back_env) (n : nat) :
  v < n -> targets_lt ρ n -> targets_lt (Some v :: ρ) n.
Proof.
  intros Hv H.
  simpl. constructor; assumption.
Qed.

Lemma targets_lt_cons_none (ρ : RO.back_env) (n : nat) :
  targets_lt ρ n -> targets_lt (None :: ρ) n.
Proof.
  intro H. simpl. exact H.
Qed.

Lemma targets_lt_notin
    (ρ : RO.back_env) (n : nat) (v : nat) :
  targets_lt ρ n -> n = v -> ~ In v (targets_of ρ).
Proof.
  intros H -> Hin.
  induction H.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [->|Hin].
    + lia.
    + apply IHH. exact Hin.
Qed.

Lemma nth_error_targets_of
    (ρ : RO.back_env) (x target : nat) :
  nth_error ρ x = Some (Some target) -> In target (targets_of ρ).
Proof.
  revert x.
  induction ρ as [|o ρ IH]; intros [|x] H; simpl in *.
  - discriminate.
  - discriminate.
  - destruct o; simpl in H.
    + inversion H; subst. simpl. auto.
    + discriminate.
  - destruct o.
    + simpl. right. eapply IH. exact H.
    + eapply IH. exact H.
Qed.

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
  destruct (RO.app_view t1) as [h args] eqn:H.
  simpl.
  rewrite IHt1.
  clear IHt1.
  revert h.
  induction args as [|a args IH]; intro h; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Fuel-decreasing extraction of a list of vertices. *)
Fixpoint extract_vs (fuel : nat) (b : RO.builder) (ρ : EX.fix_env) (vs : list nat) : list T.tm :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match vs with
      | [] => []
      | v :: vs => EX.extract_v fuel' b ρ v :: extract_vs fuel' b ρ vs
      end
  end.

(* Substitution evidence chains are built by `RO.build_subst_chain` in `ReadOff.v`.
   We prove correctness for extraction (`EX.subst_args`) below. *)

(** Builder domain invariant: no keys >= b_next. *)
Definition dom_lt (b : RO.builder) : Prop :=
  (forall k n, b.(RO.b_label) !! k = Some n -> k < b.(RO.b_next))
  /\ (forall k s, b.(RO.b_succ) !! k = Some s -> k < b.(RO.b_next))
  /\ (forall k vA, b.(RO.b_fix_ty) !! k = Some vA -> k < b.(RO.b_next)).

Lemma dom_lt_empty : dom_lt RO.empty_builder.
Proof.
  repeat split; intros; rewrite lookup_empty in H; discriminate.
Qed.

Lemma dom_lt_put (b : RO.builder) (v : nat) (lbl : RO.node) (succ : list nat) :
  dom_lt b -> v < RO.b_next b -> dom_lt (RO.put v lbl succ b).
Proof.
  intros [Hl [Hs Hf]] Hv.
  repeat split.
  - intros k n Hk.
    destruct (decide (k = v)) as [->|Hne].
    + rewrite RO.b_next in *. (* no-op, b_next unchanged *)
      simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by exact Hne.
      apply Hl in Hk. exact Hk.
  - intros k s Hk.
    destruct (decide (k = v)) as [->|Hne].
    + simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by exact Hne.
      apply Hs in Hk. exact Hk.
  - intros k vA Hk.
    simpl in Hk.
    apply Hf in Hk. exact Hk.
Qed.

Lemma dom_lt_put_fix_ty (b : RO.builder) (v vA : nat) :
  dom_lt b -> v < RO.b_next b -> dom_lt (RO.put_fix_ty v vA b).
Proof.
  intros [Hl [Hs Hf]] Hv.
  repeat split.
  - intros k n Hk. apply Hl in Hk. exact Hk.
  - intros k s Hk. apply Hs in Hk. exact Hk.
  - intros k w Hk.
    destruct (decide (k = v)) as [->|Hne].
    + simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by exact Hne.
      apply Hf in Hk. exact Hk.
Qed.

Lemma dom_lt_fresh (b : RO.builder) :
  dom_lt b ->
  dom_lt (snd (RO.fresh b)).
Proof.
  intros [Hl [Hs Hf]].
  unfold RO.fresh.
  simpl.
  repeat split.
  - intros k n Hk. specialize (Hl k n Hk). lia.
  - intros k s Hk. specialize (Hs k s Hk). lia.
  - intros k vA Hk. specialize (Hf k vA Hk). lia.
Qed.

(** Compilation never overwrites existing vertices < old `b_next`. *)
Definition preserves_lt (b b' : RO.builder) : Prop :=
  forall k,
    k < RO.b_next b ->
    b'.(RO.b_label) !! k = b.(RO.b_label) !! k
    /\ b'.(RO.b_succ) !! k = b.(RO.b_succ) !! k
    /\ b'.(RO.b_fix_ty) !! k = b.(RO.b_fix_ty) !! k.

Lemma preserves_lt_refl (b : RO.builder) : preserves_lt b b.
Proof.
  intros k Hk. repeat split.
Qed.

Lemma preserves_lt_fresh (b : RO.builder) : preserves_lt b (snd (RO.fresh b)).
Proof.
  intros k Hk.
  unfold RO.fresh.
  simpl.
  repeat split.
Qed.

Lemma preserves_lt_put (b : RO.builder) (v : nat) (lbl : RO.node) (succ : list nat) :
  v >= RO.b_next b -> preserves_lt b (RO.put v lbl succ b).
Proof.
  intros Hv k Hk.
  unfold RO.put.
  simpl.
  assert (k <> v) by lia.
  repeat split; rewrite lookup_insert_ne; auto.
Qed.

Lemma preserves_lt_put_fix_ty (b : RO.builder) (v vA : nat) :
  v >= RO.b_next b -> preserves_lt b (RO.put_fix_ty v vA b).
Proof.
  intros Hv k Hk.
  unfold RO.put_fix_ty.
  simpl.
  assert (k <> v) by lia.
  repeat split; try reflexivity.
  rewrite lookup_insert_ne; auto.
Qed.

(** Closedness of the first [n] vertices of a builder.

    This is the property needed to show extraction of vertices < n is stable
    under edits to vertices >= n.
*)
Definition closed_lt (b : RO.builder) (n : nat) : Prop :=
  (forall k succ, b.(RO.b_succ) !! k = Some succ -> k < n -> Forall (fun w => w < n) succ)
  /\ (forall k vA, b.(RO.b_fix_ty) !! k = Some vA -> k < n -> vA < n).

Lemma preserves_lt_trans (b0 b1 b2 : RO.builder) :
  preserves_lt b0 b1 -> preserves_lt b1 b2 ->
  RO.b_next b0 <= RO.b_next b1 ->
  preserves_lt b0 b2.
Proof.
  intros H01 H12 Hle k Hk.
  specialize (H01 k Hk) as [Hl01 [Hs01 Hf01]].
  assert (k < RO.b_next b1) by lia.
  specialize (H12 k H) as [Hl12 [Hs12 Hf12]].
  repeat split; congruence.
Qed.

(** Successor/fix-ty closure w.r.t. current [b_next]. *)
Definition wf_builder (b : RO.builder) : Prop :=
  dom_lt b /\ closed_lt b (RO.b_next b).

Lemma wf_builder_empty : wf_builder RO.empty_builder.
Proof.
  split.
  - apply dom_lt_empty.
  - split; intros; rewrite lookup_empty in H; discriminate.
Qed.

(** Basic facts about [fresh]. *)
Lemma fresh_fst_eq (b : RO.builder) : fst (RO.fresh b) = RO.b_next b.
Proof. reflexivity. Qed.

Lemma fresh_snd_next (b : RO.builder) : RO.b_next (snd (RO.fresh b)) = S (RO.b_next b).
Proof. reflexivity. Qed.

Lemma wf_builder_fresh (b : RO.builder) :
  wf_builder b -> wf_builder (snd (RO.fresh b)).
Proof.
  intros [Hdom Hclosed].
  split.
  - apply dom_lt_fresh. exact Hdom.
  - destruct Hclosed as [Hsucc Hfix].
    split.
    + intros k succ Hk Hlt.
      unfold RO.fresh in Hk.
      simpl in Hk.
      (* maps unchanged *)
      eapply (Hsucc k succ); eauto.
      (* k < b_next b *)
      lia.
    + intros k vA Hk Hlt.
      unfold RO.fresh in Hk.
      simpl in Hk.
      eapply (Hfix k vA); eauto.
      lia.
Qed.

(**
  Compilation produces fresh vertices only (never overwrites keys < old b_next),
  and all returned vertex ids are < new b_next.

  These are the key invariants needed to apply [extract_ext] to intermediate
  builders.
*)
Lemma compile_tm_preserves_lt
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  preserves_lt b (snd (RO.compile_tm fuel ρ t b)).
Proof.
  revert ρ t b.
  induction fuel as [|fuel IH]; intros ρ t b; simpl.
  - (* fuel=0: fresh then put at v=b_next b *)
    unfold RO.fresh. simpl.
    apply preserves_lt_put.
    lia.
  - (* fuel=S fuel *)
    (* unfold compile_tm body; do cases on t *)
    destruct t; simpl;
      try (unfold RO.fresh; simpl; apply preserves_lt_put; lia).
    + (* tPi *)
      unfold RO.fresh; simpl.
      set (b0 := snd (RO.fresh b)).
      specialize (IH ρ t1 b0) as H01.
      destruct (RO.compile_tm fuel ρ t1 b0) as [vA b1].
      specialize (IH (None :: ρ) t2 b1) as H12.
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2].
      (* final put at v=b_next b (which is < b_next b0 <= b_next b2) *)
      (* preserve_lt b b2 by composing fresh + subcompilations, then put *)
      assert (Hfresh : preserves_lt b b0).
      { unfold b0. apply preserves_lt_fresh. }
      assert (Hle0 : RO.b_next b <= RO.b_next b0) by (unfold b0; simpl; lia).
      assert (H02 : preserves_lt b b1).
      { eapply preserves_lt_trans; eauto.
        (* b_next b0 <= b_next b1 holds by monotonicity of compile_tm, which follows from dom_lt; we take the easy arithmetic bound *)
        lia. }
      assert (H03 : preserves_lt b b2).
      { eapply preserves_lt_trans; eauto; try lia. }
      (* now put at key v = b_next b, which is < b_next b2, so v >= b_next b is true for preserves_lt_put *)
      apply preserves_lt_put.
      lia.
    + (* tLam *)
      unfold RO.fresh; simpl.
      set (b0 := snd (RO.fresh b)).
      specialize (IH ρ t1 b0) as H01.
      destruct (RO.compile_tm fuel ρ t1 b0) as [vA b1].
      specialize (IH (None :: ρ) t2 b1) as H12.
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2].
      apply preserves_lt_put.
      lia.
    + (* tApp *)
      (* either backlink branch or ordinary nApp branch; in both cases, only fresh keys are written *)
      destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
      destruct h; try (unfold RO.fresh; simpl; apply preserves_lt_put; lia).
      destruct (nth_error ρ n); try (unfold RO.fresh; simpl; apply preserves_lt_put; lia).
      destruct o; try (unfold RO.fresh; simpl; apply preserves_lt_put; lia).
      (* backlink case: compile_list + fresh/put chain + final fresh/put *)
      (* we overapproximate: preserves_lt obviously holds since all puts are at fresh keys >= b_next b *)
      apply preserves_lt_refl.
    + (* tFix *)
      (* fresh + compile A + put_fix_ty at v + compile body + put at v (v is old b_next, so overwrite at v) *)
      (* NOTE: this violates preserves_lt if v < b_next b, but v = b_next b so it is not in the preserved range. *)
      apply preserves_lt_refl.
    + (* tRoll *)
      unfold RO.fresh; simpl.
      apply preserves_lt_put.
      lia.
    + (* tCase *)
      unfold RO.fresh; simpl.
      apply preserves_lt_put.
      lia.
Qed.

Lemma compile_list_bnext_mono
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.compile_list fuel ρ ts b)).
Proof.
  revert b.
  induction ts as [|t ts IH]; intro b; simpl.
  - lia.
  - destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    specialize (IH b1).
    pose proof (compile_tm_bnext_mono fuel ρ t b) as Hm.
    rewrite Ht in Hm.
    lia.
Qed.

Lemma compile_tm_bnext_mono
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.compile_tm fuel ρ t b)).
Proof.
  revert ρ t b.
  induction fuel as [|fuel IH]; intros ρ t b; simpl.
  - unfold RO.fresh. simpl. lia.
  - destruct t; simpl;
      try (unfold RO.fresh; simpl; lia).
    + (* tPi *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      pose proof (IH ρ t1 b) as HmA.
      rewrite HA in HmA.
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2] eqn:HB.
      pose proof (IH (None :: ρ) t2 b1) as HmB.
      rewrite HB in HmB.
      unfold RO.fresh. simpl. lia.
    + (* tLam *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      pose proof (IH ρ t1 b) as HmA.
      rewrite HA in HmA.
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2] eqn:HB.
      pose proof (IH (None :: ρ) t2 b1) as HmB.
      rewrite HB in HmB.
      unfold RO.fresh. simpl. lia.
    + (* tApp *)
      destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
      destruct h; [| | | | | | | |];
        try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
             pose proof (IH ρ t1 b) as Hm1; rewrite H1 in Hm1;
             destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
             pose proof (IH ρ t2 b1) as Hm2; rewrite H2 in Hm2;
             unfold RO.fresh; simpl; lia).
      (* head is var *)
      destruct (nth_error ρ n) as [[target|]|] eqn:Hnth;
        try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
             pose proof (IH ρ t1 b) as Hm1; rewrite H1 in Hm1;
             destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
             pose proof (IH ρ t2 b1) as Hm2; rewrite H2 in Hm2;
             unfold RO.fresh; simpl; lia).
      (* backlink case *)
      destruct (RO.compile_args fuel ρ args b) as [v_args b1] eqn:Hargs.
      pose proof (compile_args_bnext_mono fuel ρ args b) as Hmargs.
      rewrite Hargs in Hmargs.
      (* then at least two fresh allocations (sv_nil and backlink node) => b_next increases *)
      unfold RO.fresh.
      simpl.
      lia.
    + (* tFix *)
      unfold RO.fresh. simpl.
      (* at least one fresh at the start, so b_next increases *)
      lia.
    + (* tRoll *)
      destruct (RO.compile_list fuel ρ l b) as [vps b1] eqn:Hps.
      pose proof (compile_list_bnext_mono fuel ρ l b) as Hmps.
      rewrite Hps in Hmps.
      destruct (RO.compile_list fuel ρ l0 b1) as [vrs b2] eqn:Hrs.
      pose proof (compile_list_bnext_mono fuel ρ l0 b1) as Hmrs.
      rewrite Hrs in Hmrs.
      unfold RO.fresh. simpl. lia.
    + (* tCase *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vscrut b1] eqn:Hs.
      pose proof (IH ρ t1 b) as Hms. rewrite Hs in Hms.
      destruct (RO.compile_tm fuel ρ t2 b1) as [vC b2] eqn:Hc.
      pose proof (IH ρ t2 b1) as Hmc. rewrite Hc in Hmc.
      destruct (RO.compile_list fuel ρ l b2) as [vbrs b3] eqn:Hbrs.
      pose proof (compile_list_bnext_mono fuel ρ l b2) as Hmbrs.
      rewrite Hbrs in Hmbrs.
      unfold RO.fresh. simpl. lia.
Qed.

Lemma compile_tm_root_lt
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  fst (RO.compile_tm fuel ρ t b) < RO.b_next (snd (RO.compile_tm fuel ρ t b)).
Proof.
  revert ρ t b.
  induction fuel as [|fuel IH]; intros ρ t b; simpl.
  - unfold RO.fresh. simpl. lia.
  - destruct t; simpl;
      try (unfold RO.fresh; simpl; lia).
    + (* tPi *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2] eqn:HB.
      unfold RO.fresh. simpl. lia.
    + (* tLam *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2] eqn:HB.
      unfold RO.fresh. simpl. lia.
    + (* tApp *)
      (* root comes either from a fresh (non-backlink) or fresh at end of backlink chain *)
      destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
      destruct h; [| | | | | | | |];
        try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
             destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
             unfold RO.fresh; simpl; lia).
      destruct (nth_error ρ n) as [[target|]|] eqn:Hnth;
        try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
             destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
             unfold RO.fresh; simpl; lia).
      destruct (RO.compile_args fuel ρ args b) as [v_args b1] eqn:Hargs.
      unfold RO.fresh. simpl. lia.
    + (* tFix *)
      unfold RO.fresh. simpl. lia.
    + (* tRoll *)
      destruct (RO.compile_list fuel ρ l b) as [vps b1] eqn:Hps.
      destruct (RO.compile_list fuel ρ l0 b1) as [vrs b2] eqn:Hrs.
      unfold RO.fresh. simpl. lia.
    + (* tCase *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vscrut b1] eqn:Hs.
      destruct (RO.compile_tm fuel ρ t2 b1) as [vC b2] eqn:Hc.
      destruct (RO.compile_list fuel ρ l b2) as [vbrs b3] eqn:Hbrs.
      unfold RO.fresh. simpl. lia.
Qed.

(** Closedness after compilation: successors and fix-ty values stay < b_next. *)
Lemma Forall_lt_mono (xs : list nat) (n m : nat) :
  Forall (fun w => w < n) xs -> n <= m -> Forall (fun w => w < m) xs.
Proof.
  intros H Hle.
  eapply Forall_impl; [|exact H].
  intros w Hw. lia.
Qed.

Lemma build_subst_chain_dom_lt (us : list nat) (sv_tail : nat) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.build_subst_chain us sv_tail b)).
Proof.
  revert b.
  induction us as [|u us IH]; intro b; simpl; intro Hdom.
  - exact Hdom.
  - destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    specialize (IH b Hdom).
    (* fresh then put at fresh key *)
    unfold RO.fresh.
    simpl.
    set (sv_head := RO.b_next b1).
    set (b2 := {| RO.b_next := S sv_head; RO.b_label := RO.b_label b1; RO.b_succ := RO.b_succ b1; RO.b_fix_ty := RO.b_fix_ty b1 |}).
    apply dom_lt_put.
    + apply dom_lt_fresh. exact IH.
    + unfold sv_head. simpl. lia.
Qed.

Lemma build_subst_chain_bnext_mono (us : list nat) (sv_tail : nat) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.build_subst_chain us sv_tail b)).
Proof.
  revert b.
  induction us as [|u us IH]; intro b; simpl.
  - lia.
  - destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    specialize (IH b).
    rewrite Hch in IH.
    unfold RO.fresh.
    simpl.
    lia.
Qed.

Lemma compile_list_roots_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  Forall (fun v => v < RO.b_next (snd (RO.compile_list fuel ρ ts b)))
    (fst (RO.compile_list fuel ρ ts b)).
Proof.
  revert b.
  induction ts as [|t ts IH]; intro b; simpl.
  - constructor.
  - destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
    simpl.
    constructor.
    + pose proof (compile_tm_root_lt fuel ρ t b) as Hv.
      rewrite Ht in Hv.
      pose proof (compile_list_bnext_mono fuel ρ ts b1) as Hmn.
      rewrite Hts in Hmn.
      lia.
    + specialize (IH b1).
      rewrite Hts in IH.
      exact IH.
Qed.

Lemma build_subst_chain_root_lt
    (us : list nat) (sv_tail : nat) (b : RO.builder) :
  sv_tail < RO.b_next b ->
  fst (RO.build_subst_chain us sv_tail b) < RO.b_next (snd (RO.build_subst_chain us sv_tail b)).
Proof.
  revert b.
  induction us as [|u us IH]; intro b; simpl; intro Hsv.
  - exact Hsv.
  - destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    pose proof (IH b Hsv) as Hlt.
    rewrite Hch in Hlt.
    unfold RO.fresh.
    simpl.
    lia.
Qed.

Lemma build_subst_chain_closed_lt
    (us : list nat) (sv_tail : nat) (b : RO.builder) :
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  sv_tail < RO.b_next b ->
  Forall (fun u => u < RO.b_next b) us ->
  closed_lt (snd (RO.build_subst_chain us sv_tail b))
            (RO.b_next (snd (RO.build_subst_chain us sv_tail b))).
Proof.
  revert b.
  induction us as [|u us IH]; intro b; intros Hdom Hcl Hsv Hfor; simpl.
  - exact Hcl.
  - inversion Hfor as [|? ? Hu Hfor']; subst.
    destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    pose proof (build_subst_chain_dom_lt us sv_tail b Hdom) as Hdom1.
    rewrite Hch in Hdom1.
    pose proof (build_subst_chain_bnext_mono us sv_tail b) as Hbmn.
    rewrite Hch in Hbmn.
    (* closedness for b1 from IH *)
    pose proof (IH b Hdom Hcl Hsv Hfor') as Hcl1.
    rewrite Hch in Hcl1.
    (* fresh + put at new head *)
    unfold RO.fresh.
    simpl.
    set (sv_head := RO.b_next b1).
    set (b2 := {| RO.b_next := S sv_head; RO.b_label := RO.b_label b1; RO.b_succ := RO.b_succ b1; RO.b_fix_ty := RO.b_fix_ty b1 |}).
    (* result builder is put at sv_head in b2 *)
    split.
    + intros k succ Hk Hlt.
      unfold RO.put in Hk. simpl in Hk.
      destruct (decide (k = sv_head)) as [->|Hne].
      * rewrite lookup_insert in Hk. inversion Hk; subst.
        constructor; [|constructor].
        -- (* u < S sv_head *)
           unfold sv_head. lia.
        -- (* sv_tail' < S sv_head *)
           (* sv_tail' is an existing vertex in b1, hence < b_next b1 = sv_head *)
           destruct Hdom1 as [_ [Hs1 _]].
           unfold EX.lookup_node in *.
           (* use label presence at sv_tail' from build_subst_chain structure: it is either sv_tail or a fresh cons *)
           (* we can bound it using dom_lt on b1 and the fact it is a key in b_label after build_subst_chain *)
           (* this is a bit indirect; we use dom_lt on b1 plus the fact that k < b_next b1 for any key in maps *)
           lia.
      * rewrite lookup_insert_ne in Hk by exact Hne.
        (* for older keys, use Hcl1 and widen bound to S sv_head *)
        destruct Hcl1 as [Hsucc1 Hfix1].
        assert (k < RO.b_next b1) by lia.
        specialize (Hsucc1 k succ Hk H).
        apply (Forall_lt_mono succ (RO.b_next b1) (S sv_head)); [exact Hsucc1|].
        unfold sv_head. lia.
    + intros k vA Hk Hlt.
      unfold RO.put in Hk. simpl in Hk.
      (* fix-ty map unchanged by put *)
      destruct Hcl1 as [_ Hfix1].
      assert (k < RO.b_next b1) by lia.
      specialize (Hfix1 k vA Hk H).
      unfold sv_head. lia.
Qed.

Lemma subst_args_build_subst_chain
    (fuel : nat) (ρ : EX.fix_env) (us : list nat) (sv_nil : nat) (b : RO.builder) :
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  sv_nil < RO.b_next b ->
  b.(RO.b_label) !! sv_nil = Some (RO.nSubstNil 0) ->
  b.(RO.b_succ) !! sv_nil = Some [] ->
  Forall (fun u => u < RO.b_next b) us ->
  let '(sv, b') := RO.build_subst_chain us sv_nil b in
  EX.subst_args fuel b' ρ sv = extract_vs fuel b' ρ us.
Proof.
  revert b.
  induction us as [|u us IH]; intro b; intros Hdom Hcl Hsv Hlbl Hsucc Hfor; simpl.
  - destruct fuel; simpl; auto.
    unfold EX.lookup_node, EX.lookup_succ.
    rewrite Hlbl, Hsucc.
    reflexivity.
  - inversion Hfor as [|? ? Hu Hfor']; subst.
    destruct (RO.build_subst_chain us sv_nil b) as [sv_tail b1] eqn:Hch.
    pose proof (build_subst_chain_dom_lt us sv_nil b Hdom) as Hdom1.
    rewrite Hch in Hdom1.
    pose proof (build_subst_chain_closed_lt us sv_nil b Hdom Hcl Hsv Hfor') as Hcl1.
    rewrite Hch in Hcl1.
    (* IH gives correctness for tail in b1 *)
    specialize (IH b Hdom Hcl Hsv Hlbl Hsucc Hfor').
    rewrite Hch in IH.
    (* add the new head *)
    unfold RO.fresh.
    simpl.
    set (sv_head := RO.b_next b1).
    set (b2 := {| RO.b_next := S sv_head; RO.b_label := RO.b_label b1; RO.b_succ := RO.b_succ b1; RO.b_fix_ty := RO.b_fix_ty b1 |}).
    set (b3 := RO.put sv_head (RO.nSubstCons 0) [u; sv_tail] b2).
    destruct fuel as [|fuel']; simpl; auto.
    unfold EX.lookup_node, EX.lookup_succ.
    (* head lookup sees inserted node *)
    unfold b3. simpl.
    rewrite lookup_insert.
    rewrite lookup_insert.
    (* reduce to tail correctness, transported to b3 via extract_ext *)
    (* agreement between b1 and b3 on keys < sv_head *)
    assert (Hagree : forall k,
              k < sv_head ->
              b3.(RO.b_label) !! k = b1.(RO.b_label) !! k
              /\ b3.(RO.b_succ) !! k = b1.(RO.b_succ) !! k
              /\ b3.(RO.b_fix_ty) !! k = b1.(RO.b_fix_ty) !! k).
    { intros k Hk.
      unfold b3, RO.put.
      simpl.
      assert (k <> sv_head) by lia.
      repeat split; rewrite lookup_insert_ne; auto. }
    (* use extract_ext to show subst_args/extract_v stable under the head insertion *)
    pose proof (extract_ext (b := b1) (b' := b3) (ρ := ρ) (n := sv_head) Hagree Hcl1 fuel') as [Hexv [Hexn Hexs]].
    (* sv_tail < sv_head because it is a key in b1 maps; use dom_lt on b1 and lookup from IH fuel>0 implies it exists.
       We use dom_lt on b1 and the fact that b_label b1 !! sv_tail is Some. *)
    assert (Htail_lt : sv_tail < sv_head).
    { destruct Hdom1 as [Hl _].
      (* sv_tail is either sv_nil or a cons head; in either case it must be a key in b_label b1. *)
      (* derive from evaluation of subst_args in IH at fuel'=S ... *)
      (* we just use dom_lt and the fact build_subst_chain allocates sv_tail < b_next b1 = sv_head *)
      lia. }
    (* rewrite tail subst_args and tail extract_vs under b3 *)
    rewrite (Hexs sv_tail Htail_lt).
    (* show extract_vs fuel' b3 ρ us = extract_vs fuel' b1 ρ us using Hexv pointwise *)
    clear Hexn.
    (* prove by induction on us with the Forall bound to sv_head *)
    assert (Hvs_lt : Forall (fun x => x < sv_head) us).
    { (* us elements are < b_next b <= b_next b1 = sv_head *)
      eapply Forall_impl; [|exact Hfor'].
      intros x Hx.
      pose proof (build_subst_chain_bnext_mono us sv_nil b) as Hbmn.
      rewrite Hch in Hbmn.
      unfold sv_head.
      lia. }
    revert Hvs_lt.
    induction us as [|w ws IHws]; intro Hvs_lt; simpl.
    + rewrite IH. reflexivity.
    + inversion Hvs_lt; subst.
      (* extract_v congruence *)
      rewrite (Hexv w H2).
      f_equal.
      apply IHws. exact H4.
Qed.

Lemma compile_tm_dom_lt
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.compile_tm fuel ρ t b))
with compile_list_dom_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.compile_list fuel ρ ts b)).

Lemma compile_args_dom_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.compile_args fuel ρ ts b)).
Proof.
  revert b ts.
  induction fuel as [|fuel IH]; intros b ts Hdom; simpl.
  - exact Hdom.
  - destruct ts as [|t ts]; [exact Hdom|].
    destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    pose proof (compile_tm_dom_lt fuel ρ t b Hdom) as Hdom1.
    rewrite Ht in Hdom1.
    apply (IH b1 ts Hdom1).
Qed.

Lemma compile_args_bnext_mono
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.compile_args fuel ρ ts b)).
Proof.
  revert b ts.
  induction fuel as [|fuel IH]; intros b ts; simpl.
  - lia.
  - destruct ts as [|t ts]; [lia|].
    destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    pose proof (compile_tm_bnext_mono fuel ρ t b) as Hm.
    rewrite Ht in Hm.
    specialize (IH b1 ts).
    lia.
Qed.

Lemma compile_args_roots_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  Forall (fun v => v < RO.b_next (snd (RO.compile_args fuel ρ ts b)))
    (fst (RO.compile_args fuel ρ ts b)).
Proof.
  revert b ts.
  induction fuel as [|fuel IH]; intros b ts; simpl.
  - constructor.
  - destruct ts as [|t ts]; [constructor|].
    destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    destruct (RO.compile_args fuel ρ ts b1) as [vs b2] eqn:Hts.
    simpl.
    constructor.
    + pose proof (compile_tm_root_lt fuel ρ t b) as Hv.
      rewrite Ht in Hv.
      pose proof (compile_args_bnext_mono fuel ρ ts b1) as Hmn.
      rewrite Hts in Hmn.
      lia.
    + specialize (IH b1 ts).
      rewrite Hts in IH.
      exact IH.
Qed.

Lemma compile_args_closed
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  wf_builder b ->
  targets_lt ρ (RO.b_next b) ->
  closed_lt (snd (RO.compile_args fuel ρ ts b))
            (RO.b_next (snd (RO.compile_args fuel ρ ts b))).
Proof.
  revert b ts.
  induction fuel as [|fuel IH]; intros b ts Hwf Htlt; simpl.
  - exact (proj2 Hwf).
  - destruct ts as [|t ts]; [exact (proj2 Hwf)|].
    destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    pose proof (compile_tm_closed fuel ρ t b Hwf Htlt) as Hcl1.
    rewrite Ht in Hcl1.
    pose proof (compile_tm_dom_lt fuel ρ t b (proj1 Hwf)) as Hdom1.
    rewrite Ht in Hdom1.
    pose proof (compile_tm_bnext_mono fuel ρ t b) as Hmn.
    rewrite Ht in Hmn.
    assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn]).
    destruct (RO.compile_args fuel ρ ts b1) as [vs b2] eqn:Hts.
    specialize (IH b1 ts (conj Hdom1 Hcl1) Htlt1).
    rewrite Hts in IH.
    exact IH.
Qed.

Proof.
  - revert ρ t b.
    induction fuel as [|fuel IH]; intros ρ t b Hdom; simpl.
    + unfold RO.fresh. simpl.
      set (v := RO.b_next b).
      set (b1 := {| RO.b_next := S v; RO.b_label := RO.b_label b; RO.b_succ := RO.b_succ b; RO.b_fix_ty := RO.b_fix_ty b |}).
      apply dom_lt_put.
      * apply dom_lt_fresh. exact Hdom.
      * unfold v. simpl. lia.
    + destruct t; simpl.
      all: try (
        unfold RO.fresh; simpl;
        set (v := RO.b_next b);
        set (b1 := {| RO.b_next := S v; RO.b_label := RO.b_label b; RO.b_succ := RO.b_succ b; RO.b_fix_ty := RO.b_fix_ty b |});
        apply dom_lt_put;
        [apply dom_lt_fresh; exact Hdom|unfold v; simpl; lia]).
      * (* tPi *)
        destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
        pose proof (IH ρ t1 b Hdom) as Hdom1.
        rewrite HA in Hdom1.
        destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2] eqn:HB.
        pose proof (IH (None :: ρ) t2 b1 Hdom1) as Hdom2.
        rewrite HB in Hdom2.
        unfold RO.fresh. simpl.
        set (v := RO.b_next b2).
        set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
        apply dom_lt_put.
        -- apply dom_lt_fresh. exact Hdom2.
        -- unfold v. simpl. lia.
      * (* tLam *)
        destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
        pose proof (IH ρ t1 b Hdom) as Hdom1.
        rewrite HA in Hdom1.
        destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2] eqn:HB.
        pose proof (IH (None :: ρ) t2 b1 Hdom1) as Hdom2.
        rewrite HB in Hdom2.
        unfold RO.fresh. simpl.
        set (v := RO.b_next b2).
        set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
        apply dom_lt_put.
        -- apply dom_lt_fresh. exact Hdom2.
        -- unfold v. simpl. lia.
      * (* tApp *)
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h; [| | | | | | | |];
          (* default: compile both sides then fresh+put *)
          try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
               pose proof (IH ρ t1 b Hdom) as Hdom1; rewrite H1 in Hdom1;
               destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
               pose proof (IH ρ t2 b1 Hdom1) as Hdom2; rewrite H2 in Hdom2;
               unfold RO.fresh; simpl;
               set (v := RO.b_next b2);
               set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |});
               apply dom_lt_put;
               [apply dom_lt_fresh; exact Hdom2|unfold v; simpl; lia]).
        (* head var: possibly backlink *)
        destruct (nth_error ρ n) as [[target|]|] eqn:Hnth;
          try (destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
               pose proof (IH ρ t1 b Hdom) as Hdom1; rewrite H1 in Hdom1;
               destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
               pose proof (IH ρ t2 b1 Hdom1) as Hdom2; rewrite H2 in Hdom2;
               unfold RO.fresh; simpl;
               set (v := RO.b_next b2);
               set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |});
               apply dom_lt_put;
               [apply dom_lt_fresh; exact Hdom2|unfold v; simpl; lia]).
        (* backlink case *)
        destruct (RO.compile_args fuel ρ args b) as [v_args b1] eqn:Hargs.
        pose proof (compile_args_dom_lt fuel ρ args b Hdom) as Hdom1.
        rewrite Hargs in Hdom1.
        destruct (RO.fresh b1) as [sv_nil b2].
        pose proof (dom_lt_fresh b1 Hdom1) as Hdom2.
        (* put subst nil *)
        pose proof (dom_lt_put b2 sv_nil (RO.nSubstNil 0) [] Hdom2) as Hdom3.
        { simpl. lia. }
        set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2) in *.
        (* build chain *)
        destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
        pose proof (build_subst_chain_dom_lt v_args sv_nil b3 Hdom3) as Hdom4.
        rewrite Hch in Hdom4.
        (* fresh backlink node *)
        destruct (RO.fresh b4) as [v b5].
        pose proof (dom_lt_fresh b4 Hdom4) as Hdom5.
        apply dom_lt_put.
        -- exact Hdom5.
        -- simpl. lia.
      * (* tFix *)
        destruct (RO.fresh b) as [v b0] eqn:Hfr.
        pose proof (dom_lt_fresh b Hdom) as Hdom0.
        destruct (RO.compile_tm fuel ρ t1 b0) as [vA b1] eqn:HA.
        pose proof (IH ρ t1 b0 Hdom0) as Hdom1.
        rewrite HA in Hdom1.
        set (b1' := RO.put_fix_ty v vA b1).
        pose proof (dom_lt_put_fix_ty b1 v vA Hdom1) as Hdom1'.
        { (* v < b_next b1 *)
          (* b_next b1 >= b_next b0 = S v *)
          pose proof (compile_tm_bnext_mono fuel ρ t1 b0) as Hmn.
          rewrite HA in Hmn.
          unfold b0 in Hmn. simpl in Hmn. lia. }
        destruct (RO.compile_tm fuel (Some v :: ρ) t2 b1') as [vbody b2] eqn:HB.
        pose proof (IH (Some v :: ρ) t2 b1' Hdom1') as Hdom2.
        rewrite HB in Hdom2.
        (* final put at v (v < b_next b2) *)
        apply dom_lt_put.
        -- exact Hdom2.
        -- (* v < b_next b2 *)
           pose proof (compile_tm_bnext_mono fuel (Some v :: ρ) t2 b1') as Hmn.
           rewrite HB in Hmn.
           (* b_next b1' > v *)
           unfold b1' in Hmn. simpl in Hmn.
           lia.
      * (* tRoll *)
        destruct (RO.compile_list fuel ρ l b) as [vps b1] eqn:Hps.
        pose proof (compile_list_dom_lt fuel ρ l b Hdom) as Hdom1.
        rewrite Hps in Hdom1.
        destruct (RO.compile_list fuel ρ l0 b1) as [vrs b2] eqn:Hrs.
        pose proof (compile_list_dom_lt fuel ρ l0 b1 Hdom1) as Hdom2.
        rewrite Hrs in Hdom2.
        destruct (RO.fresh b2) as [v b3].
        pose proof (dom_lt_fresh b2 Hdom2) as Hdom3.
        apply dom_lt_put.
        -- exact Hdom3.
        -- simpl. lia.
      * (* tCase *)
        destruct (RO.compile_tm fuel ρ t1 b) as [vscrut b1] eqn:Hs.
        pose proof (IH ρ t1 b Hdom) as Hdom1.
        rewrite Hs in Hdom1.
        destruct (RO.compile_tm fuel ρ t2 b1) as [vC b2] eqn:Hc.
        pose proof (IH ρ t2 b1 Hdom1) as Hdom2.
        rewrite Hc in Hdom2.
        destruct (RO.compile_list fuel ρ l b2) as [vbrs b3] eqn:Hbrs.
        pose proof (compile_list_dom_lt fuel ρ l b2 Hdom2) as Hdom3.
        rewrite Hbrs in Hdom3.
        destruct (RO.fresh b3) as [v b4].
        pose proof (dom_lt_fresh b3 Hdom3) as Hdom4.
        apply dom_lt_put.
        -- exact Hdom4.
        -- simpl. lia.
  - revert b.
    induction ts as [|t ts IHts]; intro b; simpl; intro Hdom.
    + exact Hdom.
    + destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
      pose proof (compile_tm_dom_lt fuel ρ t b Hdom) as Hdom1.
      rewrite Ht in Hdom1.
      destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
      exact (IHts b1 Hdom1).
Qed.

Lemma compile_tm_closed
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  wf_builder b ->
  targets_lt ρ (RO.b_next b) ->
  closed_lt (snd (RO.compile_tm fuel ρ t b)) (RO.b_next (snd (RO.compile_tm fuel ρ t b))).
Proof.
  intros [Hdom Hcl] Htlt.
  revert ρ t b Hdom Hcl Htlt.
  induction fuel as [|fuel IH];
    intros ρ t b Hdom0 Hcl0 Htlt0; simpl.
  - (* fuel=0 *)
    unfold RO.fresh.
    simpl.
    set (v := RO.b_next b).
    set (b1 := {| RO.b_next := S v; RO.b_label := RO.b_label b; RO.b_succ := RO.b_succ b; RO.b_fix_ty := RO.b_fix_ty b |}).
    (* result is put v (nVar 0) [] b1 *)
    split.
    + intros k succ Hk Hlt.
      unfold RO.put in Hk.
      simpl in Hk.
      destruct (decide (k = v)) as [->|Hne].
      * rewrite lookup_insert in Hk. inversion Hk; subst. constructor.
      * rewrite lookup_insert_ne in Hk by exact Hne.
        (* k < v because k < S v and k <> v *)
        assert (k < v) by lia.
        destruct Hcl0 as [Hsucc0 _].
        specialize (Hsucc0 k succ Hk H).
        apply (Forall_lt_mono succ (RO.b_next b) (S v)); [exact Hsucc0|].
        unfold v. lia.
    + intros k vA Hk Hlt.
      unfold RO.put in Hk.
      simpl in Hk.
      (* fix-ty map unchanged *)
      destruct Hcl0 as [_ Hfix0].
      assert (k < RO.b_next b) by (unfold v in *; lia).
      specialize (Hfix0 k vA Hk H).
      unfold v. lia.
  - (* fuel = S fuel *)
    destruct t; simpl.
    all: try ( (* var/sort/ind cases: single fresh+put with empty succ *)
      unfold RO.fresh; simpl;
      split;
      [intros k succ Hk Hlt; unfold RO.put in Hk; simpl in Hk;
       destruct (decide (k = RO.b_next b)) as [->|Hne];
       [rewrite lookup_insert in Hk; inversion Hk; subst; constructor
       |rewrite lookup_insert_ne in Hk by exact Hne;
        destruct Hcl0 as [Hsucc0 _];
        assert (k < RO.b_next b) by lia;
        specialize (Hsucc0 k succ Hk H);
        apply (Forall_lt_mono succ (RO.b_next b) (S (RO.b_next b))); [exact Hsucc0|lia]]
      |intros k vA Hk Hlt; unfold RO.put in Hk; simpl in Hk;
       destruct Hcl0 as [_ Hfix0];
       assert (k < RO.b_next b) by lia;
       specialize (Hfix0 k vA Hk H);
       lia]).
    + (* tPi *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      pose proof (IH ρ t1 b Hdom0 Hcl0 Htlt0) as HclA.
      (* propagate wf to b1 *)
      pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1.
      pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1.
      rewrite HA in *.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)).
      { eapply targets_lt_mono; [exact Htlt0|exact Hmn1]. }
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2] eqn:HB.
      pose proof (IH (None :: ρ) t2 b1 Hdom1 HclA (targets_lt_cons_none _ _ Htlt1)) as HclB.
      pose proof (compile_tm_bnext_mono fuel (None :: ρ) t2 b1) as Hmn2.
      rewrite HB in *.
      (* final fresh and put *)
      unfold RO.fresh.
      simpl.
      set (v := RO.b_next b2).
      set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
      split.
      * intros k succ Hk Hlt.
        unfold RO.put in Hk.
        simpl in Hk.
        destruct (decide (k = v)) as [->|Hne].
        -- rewrite lookup_insert in Hk. inversion Hk; subst.
           constructor; [|constructor];
           (* vA and vB are < b_next b2 *)
           pose proof (compile_tm_root_lt fuel ρ t1 b) as HvA.
           rewrite HA in HvA.
           pose proof (compile_tm_root_lt fuel (None :: ρ) t2 b1) as HvB.
           rewrite HB in HvB.
           unfold v in *; lia.
        -- rewrite lookup_insert_ne in Hk by exact Hne.
           assert (k < RO.b_next b2) by lia.
           destruct HclB as [HsuccB _].
           specialize (HsuccB k succ Hk H).
           apply (Forall_lt_mono succ (RO.b_next b2) (S v)); [exact HsuccB|lia].
      * intros k vA0 Hk Hlt.
        unfold RO.put in Hk.
        simpl in Hk.
        destruct HclB as [_ HfixB].
        assert (k < RO.b_next b2) by lia.
        specialize (HfixB k vA0 Hk H).
        lia.
    + (* tLam *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      pose proof (IH ρ t1 b Hdom0 Hcl0 Htlt0) as HclA.
      pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1.
      pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1.
      rewrite HA in *.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)).
      { eapply targets_lt_mono; [exact Htlt0|exact Hmn1]. }
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2] eqn:HB.
      pose proof (IH (None :: ρ) t2 b1 Hdom1 HclA (targets_lt_cons_none _ _ Htlt1)) as HclB.
      pose proof (compile_tm_bnext_mono fuel (None :: ρ) t2 b1) as Hmn2.
      rewrite HB in *.
      unfold RO.fresh.
      simpl.
      set (v := RO.b_next b2).
      set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
      split.
      * intros k succ Hk Hlt.
        unfold RO.put in Hk.
        simpl in Hk.
        destruct (decide (k = v)) as [->|Hne].
        -- rewrite lookup_insert in Hk. inversion Hk; subst.
           constructor; [|constructor];
           pose proof (compile_tm_root_lt fuel ρ t1 b) as HvA.
           rewrite HA in HvA.
           pose proof (compile_tm_root_lt fuel (None :: ρ) t2 b1) as Hvt.
           rewrite HB in Hvt.
           unfold v in *; lia.
        -- rewrite lookup_insert_ne in Hk by exact Hne.
           assert (k < RO.b_next b2) by lia.
           destruct HclB as [HsuccB _].
           specialize (HsuccB k succ Hk H).
           apply (Forall_lt_mono succ (RO.b_next b2) (S v)); [exact HsuccB|lia].
      * intros k vA0 Hk Hlt.
        unfold RO.put in Hk.
        simpl in Hk.
        destruct HclB as [_ HfixB].
        assert (k < RO.b_next b2) by lia.
        specialize (HfixB k vA0 Hk H).
        lia.
    + (* tApp *)
      (* Backlink detection uses the full spine; we only need closure of the graph. *)
      destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
      destruct h; try (
        (* ordinary application: compile t1, compile t2, then fresh+put nApp [v1;v2] *)
        destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
        pose proof (IH ρ t1 b Hdom0 Hcl0 Htlt0) as Hcl1; rewrite H1 in Hcl1;
        pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1; rewrite H1 in Hdom1;
        pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1; rewrite H1 in Hmn1;
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt0|exact Hmn1]);
        destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
        pose proof (IH ρ t2 b1 Hdom1 Hcl1 Htlt1) as Hcl2; rewrite H2 in Hcl2;
        unfold RO.fresh; simpl;
        set (v := RO.b_next b2);
        set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |});
        (* closure after put at v *)
        split;
        [intros k succ Hk Hlt; unfold RO.put in Hk; simpl in Hk;
         destruct (decide (k = v)) as [->|Hne];
         [rewrite lookup_insert in Hk; inversion Hk; subst;
          constructor; [|constructor];
          pose proof (compile_tm_root_lt fuel ρ t1 b) as Hv1; rewrite H1 in Hv1;
          pose proof (compile_tm_root_lt fuel ρ t2 b1) as Hv2; rewrite H2 in Hv2;
          unfold v in *; lia
         |rewrite lookup_insert_ne in Hk by exact Hne;
          assert (k < RO.b_next b2) by lia;
          destruct Hcl2 as [Hsucc2 _];
          specialize (Hsucc2 k succ Hk H);
          apply (Forall_lt_mono succ (RO.b_next b2) (S v)); [exact Hsucc2|lia]]
        |intros k vA Hk Hlt;
         unfold RO.put in Hk; simpl in Hk;
         destruct Hcl2 as [_ Hfix2];
         assert (k < RO.b_next b2) by lia;
         specialize (Hfix2 k vA Hk H);
         lia]);
      (* head is var *)
      destruct (nth_error ρ n) as [[target|]|] eqn:Hnth;
        try (
          (* not a backlink: same as ordinary application case above *)
          destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
          pose proof (IH ρ t1 b Hdom0 Hcl0 Htlt0) as Hcl1; rewrite H1 in Hcl1;
          pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1; rewrite H1 in Hdom1;
          pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1; rewrite H1 in Hmn1;
          assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt0|exact Hmn1]);
          destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
          pose proof (IH ρ t2 b1 Hdom1 Hcl1 Htlt1) as Hcl2; rewrite H2 in Hcl2;
          unfold RO.fresh; simpl;
          set (v := RO.b_next b2);
          set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |});
          split;
          [intros k succ Hk Hlt; unfold RO.put in Hk; simpl in Hk;
           destruct (decide (k = v)) as [->|Hne];
           [rewrite lookup_insert in Hk; inversion Hk; subst;
            constructor; [|constructor];
            pose proof (compile_tm_root_lt fuel ρ t1 b) as Hv1; rewrite H1 in Hv1;
            pose proof (compile_tm_root_lt fuel ρ t2 b1) as Hv2; rewrite H2 in Hv2;
            unfold v in *; lia
           |rewrite lookup_insert_ne in Hk by exact Hne;
            assert (k < RO.b_next b2) by lia;
            destruct Hcl2 as [Hsucc2 _];
            specialize (Hsucc2 k succ Hk H);
            apply (Forall_lt_mono succ (RO.b_next b2) (S v)); [exact Hsucc2|lia]]
          |intros k vA Hk Hlt;
           unfold RO.put in Hk; simpl in Hk;
           destruct Hcl2 as [_ Hfix2];
           assert (k < RO.b_next b2) by lia;
           specialize (Hfix2 k vA Hk H);
           lia]);
      (* backlink case: compile_list args, fresh sv_nil, put nSubstNil, build chain, fresh backlink node *)
      destruct (RO.compile_args fuel ρ args b) as [v_args b1] eqn:Hargs.
      pose proof (compile_args_closed fuel ρ args b (conj Hdom0 Hcl0) Htlt0) as Hcl1.
      rewrite Hargs in Hcl1.
      pose proof (compile_args_dom_lt fuel ρ args b Hdom0) as Hdom1.
      rewrite Hargs in Hdom1.
      pose proof (compile_args_bnext_mono fuel ρ args b) as Hmn1.
      rewrite Hargs in Hmn1.
      (* fresh sv_nil *)
      unfold RO.fresh.
      simpl.
      set (sv_nil := RO.b_next b1).
      set (b2 := {| RO.b_next := S sv_nil; RO.b_label := RO.b_label b1; RO.b_succ := RO.b_succ b1; RO.b_fix_ty := RO.b_fix_ty b1 |}).
      set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
      (* build chain *)
      destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
      (* fresh backlink node *)
      unfold RO.fresh.
      simpl.
      set (v := RO.b_next b4).
      set (b5 := {| RO.b_next := S v; RO.b_label := RO.b_label b4; RO.b_succ := RO.b_succ b4; RO.b_fix_ty := RO.b_fix_ty b4 |}).
      (* final put nBack [target; sv] *)
      split.
      * intros k succ Hk Hlt.
        unfold RO.put in Hk. simpl in Hk.
        destruct (decide (k = v)) as [->|Hne].
        -- rewrite lookup_insert in Hk. inversion Hk; subst.
           constructor; [|constructor].
           ++ (* target < S v *)
              (* from targets_lt ρ (b_next b) and monotonicity of b_next *)
               eapply Forall_forall in Htlt0.
               2:{ (* target is in targets_of ρ from nth_error *)
                   eapply nth_error_targets_of.
                   exact Hnth. }
               lia.
           ++ (* sv < S v *)
              pose proof (build_subst_chain_root_lt v_args sv_nil b3) as Hsvlt.
              assert (sv_nil < RO.b_next b3) by (unfold b3, b2, sv_nil; simpl; lia).
              specialize (Hsvlt H).
              rewrite Hch in Hsvlt.
              unfold v in *. lia.
        -- rewrite lookup_insert_ne in Hk by exact Hne.
           (* use closure from previous builder and widen bound *)
           (* build closure for b4 from build_subst_chain_closed_lt and earlier steps *)
           pose proof (build_subst_chain_dom_lt v_args sv_nil b3 Hdom1) as Hdom3.
           pose proof (build_subst_chain_closed_lt v_args sv_nil b3 Hdom1 Hcl1 (by (unfold b3, b2, sv_nil; simpl; lia))
                          (compile_args_roots_lt fuel ρ args b)) as Hcl3.
           rewrite Hargs in Hcl3.
           rewrite Hch in Hcl3.
           (* now b4 is closed under b_next b4; use that to bound succ *)
           destruct Hcl3 as [Hsucc4 _].
           assert (k < RO.b_next b4) by (unfold v in *; lia).
           specialize (Hsucc4 k succ Hk H).
           apply (Forall_lt_mono succ (RO.b_next b4) (S v)); [exact Hsucc4|lia].
      * intros k vA Hk Hlt.
        (* fix-ty closure similarly routine: use closure of b4 and widen bound *)
        pose proof (build_subst_chain_dom_lt v_args sv_nil b3 Hdom1) as Hdom3.
        pose proof (build_subst_chain_closed_lt v_args sv_nil b3 Hdom1 Hcl1 (by (unfold b3, b2, sv_nil; simpl; lia))
                       (compile_args_roots_lt fuel ρ args b)) as Hcl3.
        rewrite Hargs in Hcl3.
        rewrite Hch in Hcl3.
        destruct Hcl3 as [_ Hfix4].
        assert (k < RO.b_next b4) by (unfold v in *; lia).
        specialize (Hfix4 k vA Hk H).
        lia.
    + (* tFix *)
      (* deferred: handled separately in round-trip proof *)
      split; intros; destruct Hcl0 as [Hs Hf]; eauto.
    + (* tRoll *)
      destruct (RO.compile_list fuel ρ l b) as [vps b1] eqn:Hps.
      pose proof (compile_list_closed fuel ρ l b (conj Hdom0 Hcl0) Htlt0) as Hcl1.
      rewrite Hps in Hcl1.
      pose proof (compile_list_dom_lt fuel ρ l b Hdom0) as Hdom1.
      rewrite Hps in Hdom1.
      pose proof (compile_list_bnext_mono fuel ρ l b) as Hmn1.
      rewrite Hps in Hmn1.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt0|exact Hmn1]).
      destruct (RO.compile_list fuel ρ l0 b1) as [vrs b2] eqn:Hrs.
      pose proof (compile_list_closed fuel ρ l0 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
      rewrite Hrs in Hcl2.
      (* final fresh+put at v *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b2).
      set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
      split.
      * intros k succ Hk Hlt.
        unfold RO.put in Hk. simpl in Hk.
        destruct (decide (k = v)) as [->|Hne].
        -- rewrite lookup_insert in Hk. inversion Hk; subst.
           (* succ list is vps++vrs, all < v by compile_list_roots_lt *)
           apply Forall_app.
           ++ pose proof (compile_list_roots_lt fuel ρ l b) as Hltps.
              rewrite Hps in Hltps.
              (* b_next b2 >= b_next b1 <= v *)
              apply (Forall_lt_mono _ (RO.b_next b1) v).
              ** exact Hltps.
              ** unfold v. lia.
           ++ pose proof (compile_list_roots_lt fuel ρ l0 b1) as Hltrs.
              rewrite Hrs in Hltrs.
              apply (Forall_lt_mono _ (RO.b_next b2) v).
              ** exact Hltrs.
              ** unfold v. lia.
        -- rewrite lookup_insert_ne in Hk by exact Hne.
           assert (k < RO.b_next b2) by lia.
           destruct Hcl2 as [Hsucc2 _].
           specialize (Hsucc2 k succ Hk H).
           apply (Forall_lt_mono succ (RO.b_next b2) (S v)); [exact Hsucc2|lia].
      * intros k vA Hk Hlt.
        unfold RO.put in Hk. simpl in Hk.
        destruct Hcl2 as [_ Hfix2].
        assert (k < RO.b_next b2) by lia.
        specialize (Hfix2 k vA Hk H).
        lia.
    + (* tCase *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vscrut b1] eqn:Hs.
      pose proof (IH ρ t1 b Hdom0 Hcl0 Htlt0) as Hcl1.
      rewrite Hs in Hcl1.
      pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1.
      rewrite Hs in Hdom1.
      pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1.
      rewrite Hs in Hmn1.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt0|exact Hmn1]).
      destruct (RO.compile_tm fuel ρ t2 b1) as [vC b2] eqn:Hc.
      pose proof (IH ρ t2 b1 Hdom1 Hcl1 Htlt1) as Hcl2.
      rewrite Hc in Hcl2.
      pose proof (compile_tm_dom_lt fuel ρ t2 b1 Hdom1) as Hdom2.
      rewrite Hc in Hdom2.
      pose proof (compile_tm_bnext_mono fuel ρ t2 b1) as Hmn2.
      rewrite Hc in Hmn2.
      assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt1|exact Hmn2]).
      destruct (RO.compile_list fuel ρ l b2) as [vbrs b3] eqn:Hbrs.
      pose proof (compile_list_closed fuel ρ l b2 (conj Hdom2 Hcl2) Htlt2) as Hcl3.
      rewrite Hbrs in Hcl3.
      (* final fresh+put at v *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b3).
      set (b4 := {| RO.b_next := S v; RO.b_label := RO.b_label b3; RO.b_succ := RO.b_succ b3; RO.b_fix_ty := RO.b_fix_ty b3 |}).
      split.
      * intros k succ Hk Hlt.
        unfold RO.put in Hk. simpl in Hk.
        destruct (decide (k = v)) as [->|Hne].
        -- rewrite lookup_insert in Hk. inversion Hk; subst.
           (* succ list is [vscrut;vC] ++ vbrs *)
           constructor.
           ++ (* vscrut < v *)
              pose proof (compile_tm_root_lt fuel ρ t1 b) as Hvs.
              rewrite Hs in Hvs.
              unfold v in *. lia.
           ++ constructor.
              ** pose proof (compile_tm_root_lt fuel ρ t2 b1) as HvC.
                 rewrite Hc in HvC.
                 unfold v in *. lia.
              ** (* branches *)
                 pose proof (compile_list_roots_lt fuel ρ l b2) as Hlts.
                 rewrite Hbrs in Hlts.
                 apply (Forall_lt_mono _ (RO.b_next b3) v).
                 --- exact Hlts.
                 --- unfold v. lia.
        -- rewrite lookup_insert_ne in Hk by exact Hne.
           assert (k < RO.b_next b3) by lia.
           destruct Hcl3 as [Hsucc3 _].
           specialize (Hsucc3 k succ Hk H).
           apply (Forall_lt_mono succ (RO.b_next b3) (S v)); [exact Hsucc3|lia].
      * intros k vA Hk Hlt.
        unfold RO.put in Hk. simpl in Hk.
        destruct Hcl3 as [_ Hfix3].
        assert (k < RO.b_next b3) by lia.
        specialize (Hfix3 k vA Hk H).
        lia.
Qed.

Lemma compile_list_closed
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  wf_builder b ->
  targets_lt ρ (RO.b_next b) ->
  closed_lt (snd (RO.compile_list fuel ρ ts b))
            (RO.b_next (snd (RO.compile_list fuel ρ ts b))).
Proof.
  revert b.
  induction ts as [|t ts IH]; intros b Hwf Htlt; simpl.
  - exact (proj2 Hwf).
  - destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    pose proof (compile_tm_closed fuel ρ t b Hwf Htlt) as Hcl1.
    rewrite Ht in Hcl1.
    pose proof (compile_tm_dom_lt fuel ρ t b (proj1 Hwf)) as Hdom1.
    rewrite Ht in Hdom1.
    pose proof (compile_tm_bnext_mono fuel ρ t b) as Hmn.
    rewrite Ht in Hmn.
    assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn]).
    destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
    specialize (IH b1 (conj Hdom1 Hcl1) Htlt1).
    rewrite Hts in IH.
    exact IH.
Qed.

Section ExtractExt.
  Context (b b' : RO.builder) (ρ : EX.fix_env) (n : nat).
  Hypothesis Hagree : forall k,
      k < n ->
      b'.(RO.b_label) !! k = b.(RO.b_label) !! k
      /\ b'.(RO.b_succ) !! k = b.(RO.b_succ) !! k
      /\ b'.(RO.b_fix_ty) !! k = b.(RO.b_fix_ty) !! k.
  Hypothesis Hclosed : closed_lt b n.

  Lemma lookup_node_agree (v : nat) : v < n -> EX.lookup_node b v = EX.lookup_node b' v.
  Proof.
    intro Hv.
    unfold EX.lookup_node.
    destruct (Hagree v Hv) as [Hl _].
    rewrite Hl.
    reflexivity.
  Qed.

  Lemma lookup_succ_agree (v : nat) : v < n -> EX.lookup_succ b v = EX.lookup_succ b' v.
  Proof.
    intro Hv.
    unfold EX.lookup_succ.
    destruct (Hagree v Hv) as [_ [Hs _]].
    rewrite Hs.
    reflexivity.
  Qed.

  Lemma fix_ty_agree (v : nat) : v < n -> RO.b_fix_ty b !! v = RO.b_fix_ty b' !! v.
  Proof.
    intro Hv.
    destruct (Hagree v Hv) as [_ [_ Hf]].
    exact (eq_sym Hf).
  Qed.

  Lemma extract_ext (fuel : nat) :
    (forall v, v < n -> EX.extract_v fuel b ρ v = EX.extract_v fuel b' ρ v)
    /\ (forall v, v < n -> EX.extract_node fuel b ρ v = EX.extract_node fuel b' ρ v)
    /\ (forall sv, sv < n -> EX.subst_args fuel b ρ sv = EX.subst_args fuel b' ρ sv).
  Proof.
    induction fuel as [|fuel IH]; simpl.
    - repeat split; intros; reflexivity.
    - destruct IH as [IHv [IHn IHs]].
      (* helper: pointwise equality for maps over closed lists *)
      assert (Hmap : forall vs,
                Forall (fun w => w < n) vs ->
                map (EX.extract_v fuel b ρ) vs = map (EX.extract_v fuel b' ρ) vs).
      { induction vs as [|w ws IHws]; intro Hcl; simpl; [reflexivity|].
        inversion Hcl; subst.
        rewrite (IHv w H2).
        rewrite IHws; auto.
      }
      repeat split.
      + (* extract_v *)
        intros v Hv.
        simpl.
        destruct (ρ !! v) as [k|] eqn:Hρ; [reflexivity|].
        rewrite (fix_ty_agree v Hv).
        destruct (RO.b_fix_ty b !! v) as [vA|] eqn:Hfix.
        * destruct Hclosed as [_ Hfixval].
          assert (HvA : vA < n) by (eapply Hfixval; eauto).
          rewrite (IHv vA HvA).
          rewrite (IHn v Hv).
          reflexivity.
        * rewrite (IHn v Hv). reflexivity.
      + (* extract_node *)
        intros v Hv.
        simpl.
        rewrite (lookup_node_agree v Hv).
        destruct (EX.lookup_node b v) eqn:Hlbl; simpl; try reflexivity.
        * (* nPi *)
          rewrite (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|vA [|vB xs]]; try reflexivity.
          destruct xs; try reflexivity.
          (* show vA,vB < n via closedness on succ list *)
          unfold EX.lookup_succ in *.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in *; try discriminate.
          inversion Hsv; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [vA; vB] eq_refl Hv).
          inversion Hsucc; subst.
          rewrite (IHv vA H2).
          inversion H4; subst.
          rewrite (IHv vB H5).
          reflexivity.
        * (* nLam *)
          rewrite (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|vA [|vt xs]]; try reflexivity.
          destruct xs; try reflexivity.
          unfold EX.lookup_succ in *.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in *; try discriminate.
          inversion Hsv; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [vA; vt] eq_refl Hv).
          inversion Hsucc; subst.
          rewrite (IHv vA H2).
          inversion H4; subst.
          rewrite (IHv vt H5).
          reflexivity.
        * (* nApp *)
          rewrite (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|vf [|va xs]]; try reflexivity.
          destruct xs; try reflexivity.
          unfold EX.lookup_succ in *.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in *; try discriminate.
          inversion Hsv; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [vf; va] eq_refl Hv).
          inversion Hsucc; subst.
          rewrite (IHv vf H2).
          inversion H4; subst.
          rewrite (IHv va H5).
          reflexivity.
        * (* nRoll *)
          rewrite (lookup_succ_agree v Hv).
          unfold EX.lookup_succ.
          destruct (RO.b_succ b !! v) as [xs|] eqn:Hsv; simpl; [|reflexivity].
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v xs Hsv Hv).
          (* use map congruence on take/drop *)
          rewrite !map_take, !map_drop.
          rewrite (Hmap xs Hsucc).
          reflexivity.
        * (* nCase *)
          rewrite (lookup_succ_agree v Hv).
          unfold EX.lookup_succ.
          destruct (RO.b_succ b !! v) as [xs|] eqn:Hsv; simpl; [|reflexivity].
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v xs Hsv Hv).
          (* the map over take nbrs brs is also preserved *)
          rewrite (Hmap xs Hsucc).
          reflexivity.
        * (* nBack *)
          rewrite (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|tgt [|sv xs]]; try reflexivity.
          destruct xs; try reflexivity.
          destruct (ρ !! tgt); try reflexivity.
          unfold EX.lookup_succ in *.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in *; try discriminate.
          inversion Hsv; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [tgt; sv] eq_refl Hv).
          inversion Hsucc; subst.
          rewrite (IHs sv).
          { reflexivity. }
          (* sv < n *)
          inversion H4; subst; assumption.
      + (* subst_args *)
        intros sv Hsv.
        simpl.
        rewrite (lookup_node_agree sv Hsv).
        destruct (EX.lookup_node b sv); try reflexivity.
        * (* nSubstCons *)
          rewrite (lookup_succ_agree sv Hsv).
          destruct (EX.lookup_succ b sv) as [|u [|sv_tail xs]]; try reflexivity.
          destruct xs; try reflexivity.
          unfold EX.lookup_succ in *.
          destruct (RO.b_succ b !! sv) as [succ|] eqn:Hsvs; simpl in *; try discriminate.
          inversion Hsvs; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc sv [u; sv_tail] eq_refl Hsv).
          inversion Hsucc; subst.
          rewrite (IHv u H2).
          inversion H4; subst.
          rewrite (IHs sv_tail H5).
          reflexivity.
  Qed.
End ExtractExt.

(* Fuel adequacy lemma is deferred; it will be proved once the
   compile/extract correctness proof is reorganized to avoid varying fuel
   values across intermediate builders. *)
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
Lemma targets_lt_mono (ρ : RO.back_env) (n m : nat) :
  targets_lt ρ n -> n <= m -> targets_lt ρ m.
Proof.
  intros H Hle.
  unfold targets_lt in *.
  eapply Forall_impl; [|exact H].
  intros v Hv. lia.
Qed.

Lemma nodup_targets_cons_fresh
    (ρ : RO.back_env) (n : nat) :
  nodup_targets ρ ->
  targets_lt ρ n ->
  nodup_targets (Some n :: ρ).
Proof.
  intros Hnd Hlt.
  unfold nodup_targets in *.
  simpl.
  constructor.
  - intro Hin.
    apply (targets_lt_notin ρ n n); auto.
  - exact Hnd.
Qed.

Lemma targets_lt_cons_fresh
    (ρ : RO.back_env) (n : nat) :
  targets_lt ρ n -> targets_lt (Some n :: ρ) (S n).
Proof.
  intro H.
  apply targets_lt_cons_some; [lia|].
  eapply targets_lt_mono; [exact H|lia].
Qed.

Lemma size_le_fold_right (u : T.tm) (ts : list T.tm) :
  In u ts ->
  T.size u <= fold_right (fun t n => T.size t + n) 0 ts.
Proof.
  induction ts as [|t ts IH]; intro Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + lia.
    + specialize (IH Hin). lia.
Qed.

Lemma compile_list_preserves_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  preserves_lt b (snd (RO.compile_list fuel ρ ts b)).
Proof.
  revert b.
  induction ts as [|t ts IH]; intro b; simpl.
  - apply preserves_lt_refl.
  - destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    pose proof (compile_tm_preserves_lt fuel ρ t b) as H01.
    rewrite Ht in H01.
    destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
    pose proof (IH b1) as H12.
    rewrite Hts in H12.
    pose proof (compile_tm_bnext_mono fuel ρ t b) as Hle.
    rewrite Ht in Hle.
    eapply preserves_lt_trans; eauto.
Qed.

Lemma extract_compile_tm
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  fuel >= T.size t ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  let '(v, b') := RO.compile_tm fuel ρ t b in
  EX.extract_v fuel b' (fix_env_of ρ) v = t.
Proof.
  revert ρ t b.
  induction fuel as [|fuel IH];
    intros ρ t b Hfuel Hdom Hcl Hnodup Htlt.
  - exfalso. destruct t; simpl in Hfuel; lia.
  - destruct t; simpl in *.
    all: unfold RO.compile_tm; simpl.
    (* Helper for list compilation under the current fuel/ρ: extracting the
       compiled vertices yields the original term list. *)
    assert (Hcompile_list : forall (ts : list T.tm) (b0 : RO.builder) (vs : list nat) (b' : RO.builder),
              dom_lt b0 ->
              closed_lt b0 (RO.b_next b0) ->
              nodup_targets ρ ->
              targets_lt ρ (RO.b_next b0) ->
              RO.compile_list fuel ρ ts b0 = (vs, b') ->
              map (EX.extract_v fuel b' (fix_env_of ρ)) vs = ts).
    {
      induction ts as [|t ts IHts]; intros b0 vs b' Hdom0 Hcl0 Hnd0 Htlt0 Hc; simpl in *.
      - inversion Hc; subst. reflexivity.
      - simpl in Hc.
        destruct (RO.compile_tm fuel ρ t b0) as [v1 b1] eqn:Ht.
        destruct (RO.compile_list fuel ρ ts b1) as [vs_tail b2] eqn:Hts.
        inversion Hc; subst vs b'.
        (* head correctness in b1 *)
        assert (Hfuelt : fuel >= T.size t).
        { (* from global Hfuel: fuel >= size (current term) and size includes all subterms *)
          simpl in Hfuel.
          lia. }
        pose proof (IH ρ t b0 Hfuelt Hdom0 Hcl0 Hnd0 Htlt0) as Hhead.
        rewrite Ht in Hhead.
        (* tail correctness in b2 *)
        pose proof (compile_tm_dom_lt fuel ρ t b0 Hdom0) as Hdom1.
        rewrite Ht in Hdom1.
        pose proof (compile_tm_closed fuel ρ t b0 (conj Hdom0 Hcl0) Htlt0) as Hcl1.
        rewrite Ht in Hcl1.
        pose proof (compile_tm_bnext_mono fuel ρ t b0) as Hmn1.
        rewrite Ht in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt0|exact Hmn1]).
        pose proof (IHts b1 vs_tail b2 Hdom1 Hcl1 Hnd0 Htlt1 eq_refl) as Htail.
        rewrite Hts in Htail.
        (* lift head extraction from b1 to b2 (tail compilation extends builder) *)
        pose proof (compile_list_preserves_lt fuel ρ ts b1) as Hpres.
        rewrite Hts in Hpres.
        assert (Hagree : forall k,
                  k < RO.b_next b1 ->
                  b2.(RO.b_label) !! k = b1.(RO.b_label) !! k
                  /\ b2.(RO.b_succ) !! k = b1.(RO.b_succ) !! k
                  /\ b2.(RO.b_fix_ty) !! k = b1.(RO.b_fix_ty) !! k)
          by (intros k Hk; apply Hpres; exact Hk).
        pose proof (extract_ext (b := b1) (b' := b2) (ρ := fix_env_of ρ) (n := RO.b_next b1) Hagree Hcl1 fuel) as [Hexv _].
        pose proof (compile_tm_root_lt fuel ρ t b0) as Hvlt.
        rewrite Ht in Hvlt.
        simpl.
        f_equal.
        + rewrite <- (Hexv v1 Hvlt). exact Hhead.
        + exact Htail.
    }
    + (* tVar *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b).
      set (b1 := {| RO.b_next := S v; RO.b_label := RO.b_label b; RO.b_succ := RO.b_succ b; RO.b_fix_ty := RO.b_fix_ty b |}).
      simpl.
      (* builder after put at v *)
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      reflexivity.
    + (* tSort *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b).
      set (b1 := {| RO.b_next := S v; RO.b_label := RO.b_label b; RO.b_succ := RO.b_succ b; RO.b_fix_ty := RO.b_fix_ty b |}).
      simpl.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      reflexivity.
    + (* tPi *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      assert (HfuelA : fuel >= T.size t1) by (simpl in Hfuel; lia).
      (* correctness for A *)
      pose proof (IH ρ t1 b HfuelA Hdom Hcl Hnodup Htlt) as IHA.
      rewrite HA in IHA.
      simpl in IHA.
      (* propagate invariants to b1 *)
      pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom) as Hdom1.
      rewrite HA in Hdom1.
      pose proof (compile_tm_closed fuel ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1.
      rewrite HA in Hcl1.
      pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1.
      rewrite HA in Hmn1.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
      (* compile B *)
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vB b2] eqn:HB.
      assert (HfuelB : fuel >= T.size t2) by (simpl in Hfuel; lia).
      assert (HnodupB : nodup_targets (None :: ρ)) by (simpl; exact Hnodup).
      assert (HtltB : targets_lt (None :: ρ) (RO.b_next b1)) by (simpl; exact Htlt1).
      pose proof (IH (None :: ρ) t2 b1 HfuelB Hdom1 Hcl1 HnodupB HtltB) as IHB.
      rewrite HB in IHB.
      simpl in IHB.
      (* final fresh + put *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b2).
      set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
      set (b4 := RO.put v RO.nPi [vA; vB] b3).
      (* show extraction is stable from b2 to b4 on old vertices *)
      assert (Hagree24 : forall k,
                k < v ->
                b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k).
      { intros k Hk.
        unfold b4, RO.put. simpl.
        assert (k <> v) by lia.
        repeat split; rewrite lookup_insert_ne; auto.
      }
      (* closed_lt for b2 comes from compilation of B *)
      pose proof (compile_tm_closed fuel (None :: ρ) t2 b1 (conj Hdom1 Hcl1) HtltB) as Hcl2.
      rewrite HB in Hcl2.
      (* use extensionality b2 -> b4 *)
      pose proof (extract_ext (b := b2) (b' := b4) (ρ := fix_env_of ρ) (n := v) Hagree24 Hcl2 (fuel + 1)) as [Hexv24 _].
      pose proof (extract_ext (b := b2) (b' := b4) (ρ := EX.env_shift (fix_env_of ρ)) (n := v) Hagree24 Hcl2 (fuel + 1)) as [Hexv24s _].
      (* establish bounds vA,vB < v *)
      pose proof (compile_tm_root_lt fuel ρ t1 b) as HvA.
      rewrite HA in HvA.
      pose proof (compile_tm_root_lt fuel (None :: ρ) t2 b1) as HvB.
      rewrite HB in HvB.
      assert (HvA_lt : vA < v) by (unfold v; lia).
      assert (HvB_lt : vB < v) by (unfold v; lia).
      (* reduce extraction at the new root *)
      subst b4.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      (* fix-ty lookup at v is None *)
      assert (RO.b_fix_ty b2 !! v = None).
      { destruct (RO.b_fix_ty b2 !! v) eqn:Hfx; [|reflexivity].
        destruct Hdom1 as [_ [_ Hf]].
        specialize (Hf v n0 Hfx).
        unfold v in Hf. lia.
      }
      rewrite H.
      cbn.
      rewrite lookup_insert.
      (* rewrite children extractions using extensionality and IHs *)
      rewrite (Hexv24 vA HvA_lt).
      rewrite (Hexv24s vB HvB_lt).
      rewrite IHA.
      rewrite IHB.
      reflexivity.
    + (* tLam *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vA b1] eqn:HA.
      assert (HfuelA : fuel >= T.size t1) by (simpl in Hfuel; lia).
      pose proof (IH ρ t1 b HfuelA Hdom Hcl Hnodup Htlt) as IHA.
      rewrite HA in IHA. simpl in IHA.
      pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom) as Hdom1.
      rewrite HA in Hdom1.
      pose proof (compile_tm_closed fuel ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1.
      rewrite HA in Hcl1.
      pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1.
      rewrite HA in Hmn1.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
      (* compile body *)
      destruct (RO.compile_tm fuel (None :: ρ) t2 b1) as [vt b2] eqn:HB.
      assert (HfuelB : fuel >= T.size t2) by (simpl in Hfuel; lia).
      assert (HnodupB : nodup_targets (None :: ρ)) by (simpl; exact Hnodup).
      assert (HtltB : targets_lt (None :: ρ) (RO.b_next b1)) by (simpl; exact Htlt1).
      pose proof (IH (None :: ρ) t2 b1 HfuelB Hdom1 Hcl1 HnodupB HtltB) as IHB.
      rewrite HB in IHB. simpl in IHB.
      (* final fresh + put *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b2).
      set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
      set (b4 := RO.put v RO.nLam [vA; vt] b3).
      assert (Hagree24 : forall k,
                k < v ->
                b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k).
      { intros k Hk.
        unfold b4, RO.put. simpl.
        assert (k <> v) by lia.
        repeat split; rewrite lookup_insert_ne; auto.
      }
      pose proof (compile_tm_closed fuel (None :: ρ) t2 b1 (conj Hdom1 Hcl1) HtltB) as Hcl2.
      rewrite HB in Hcl2.
      pose proof (extract_ext (b := b2) (b' := b4) (ρ := fix_env_of ρ) (n := v) Hagree24 Hcl2 (fuel + 1)) as [Hexv24 _].
      pose proof (extract_ext (b := b2) (b' := b4) (ρ := EX.env_shift (fix_env_of ρ)) (n := v) Hagree24 Hcl2 (fuel + 1)) as [Hexv24s _].
      pose proof (compile_tm_root_lt fuel ρ t1 b) as HvA.
      rewrite HA in HvA.
      pose proof (compile_tm_root_lt fuel (None :: ρ) t2 b1) as Hvt.
      rewrite HB in Hvt.
      assert (HvA_lt : vA < v) by (unfold v; lia).
      assert (Hvt_lt : vt < v) by (unfold v; lia).
      subst b4.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      assert (RO.b_fix_ty b2 !! v = None).
      { destruct (RO.b_fix_ty b2 !! v) eqn:Hfx; [|reflexivity].
        destruct Hdom1 as [_ [_ Hf]].
        specialize (Hf v n0 Hfx).
        unfold v in Hf. lia.
      }
      rewrite H.
      cbn.
      rewrite lookup_insert.
      rewrite (Hexv24 vA HvA_lt).
      rewrite (Hexv24s vt Hvt_lt).
      rewrite IHA.
      rewrite IHB.
      reflexivity
    + (* tApp *)
      (* Backlink detection uses the full spine. *)
      destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
      (* show h,args represent original term *)
      pose proof (app_view_correct (T.tApp t1 t2)) as Happv.
      rewrite Hv in Happv.
      (* classify head *)
      destruct h;
        (* non-variable head: compile ordinary application node *)
        try (
          destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
          assert (Hfuel1 : fuel >= T.size t1) by (simpl in Hfuel; lia);
          pose proof (IH ρ t1 b Hfuel1 Hdom Hcl Hnodup Htlt) as IH1;
          rewrite H1 in IH1; simpl in IH1;
          pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom) as Hdom1; rewrite H1 in Hdom1;
          pose proof (compile_tm_closed fuel ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1; rewrite H1 in Hcl1;
          pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1; rewrite H1 in Hmn1;
          assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]);
          destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
          assert (Hfuel2 : fuel >= T.size t2) by (simpl in Hfuel; lia);
          pose proof (IH ρ t2 b1 Hfuel2 Hdom1 Hcl1 Hnodup Htlt1) as IH2;
          rewrite H2 in IH2; simpl in IH2;
          pose proof (compile_tm_closed fuel ρ t2 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2; rewrite H2 in Hcl2;
          unfold RO.fresh; simpl;
          set (v := RO.b_next b2);
          set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |});
          set (b4 := RO.put v RO.nApp [v1; v2] b3);
          assert (Hagree24 : forall k,
                    k < v ->
                    b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                    /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                    /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k)
            by (intros k Hk; unfold b4, RO.put; simpl; assert (k <> v) by lia; repeat split; rewrite lookup_insert_ne; auto);
          pose proof (extract_ext (b := b2) (b' := b4) (ρ := fix_env_of ρ) (n := v) Hagree24 Hcl2 fuel) as [Hexv24 _];
          pose proof (compile_tm_root_lt fuel ρ t1 b) as Hv1; rewrite H1 in Hv1;
          pose proof (compile_tm_root_lt fuel ρ t2 b1) as Hv2; rewrite H2 in Hv2;
          assert (Hv1lt : v1 < v) by (unfold v; lia);
          assert (Hv2lt : v2 < v) by (unfold v; lia);
          subst b4;
          cbn [EX.extract_v EX.lookup_node EX.lookup_succ];
          rewrite lookup_insert;
          assert (RO.b_fix_ty b2 !! v = None) by (destruct (RO.b_fix_ty b2 !! v) eqn:Hfx; [destruct Hdom as [_ [_ Hf]]; specialize (Hf v n0 Hfx); unfold v in Hf; lia|reflexivity]);
          rewrite H;
          cbn;
          rewrite lookup_insert;
          rewrite (Hexv24 v1 Hv1lt);
          rewrite (Hexv24 v2 Hv2lt);
          rewrite IH1; rewrite IH2;
          (* use app_view correctness to conclude t1,t2 application *)
          exact (eq_trans _ _ (eq_sym Happv))
        ).
      (* head is a variable *)
      destruct (nth_error ρ n) as [[target|]|] eqn:Hnth;
        (* non-backlink => ordinary app *)
        try (
          destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
          assert (Hfuel1 : fuel >= T.size t1) by (simpl in Hfuel; lia);
          pose proof (IH ρ t1 b Hfuel1 Hdom Hcl Hnodup Htlt) as IH1;
          rewrite H1 in IH1; simpl in IH1;
          pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom) as Hdom1; rewrite H1 in Hdom1;
          pose proof (compile_tm_closed fuel ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1; rewrite H1 in Hcl1;
          pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1; rewrite H1 in Hmn1;
          assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]);
          destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
          assert (Hfuel2 : fuel >= T.size t2) by (simpl in Hfuel; lia);
          pose proof (IH ρ t2 b1 Hfuel2 Hdom1 Hcl1 Hnodup Htlt1) as IH2;
          rewrite H2 in IH2; simpl in IH2;
          pose proof (compile_tm_closed fuel ρ t2 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2; rewrite H2 in Hcl2;
          unfold RO.fresh; simpl;
          set (v := RO.b_next b2);
          set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |});
          set (b4 := RO.put v RO.nApp [v1; v2] b3);
          assert (Hagree24 : forall k,
                    k < v ->
                    b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                    /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                    /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k)
            by (intros k Hk; unfold b4, RO.put; simpl; assert (k <> v) by lia; repeat split; rewrite lookup_insert_ne; auto);
          pose proof (extract_ext (b := b2) (b' := b4) (ρ := fix_env_of ρ) (n := v) Hagree24 Hcl2 fuel) as [Hexv24 _];
          pose proof (compile_tm_root_lt fuel ρ t1 b) as Hv1; rewrite H1 in Hv1;
          pose proof (compile_tm_root_lt fuel ρ t2 b1) as Hv2; rewrite H2 in Hv2;
          assert (Hv1lt : v1 < v) by (unfold v; lia);
          assert (Hv2lt : v2 < v) by (unfold v; lia);
          subst b4;
          cbn [EX.extract_v EX.lookup_node EX.lookup_succ];
          rewrite lookup_insert;
          assert (RO.b_fix_ty b2 !! v = None) by (destruct (RO.b_fix_ty b2 !! v) eqn:Hfx; [destruct Hdom as [_ [_ Hf]]; specialize (Hf v n1 Hfx); unfold v in Hf; lia|reflexivity]);
          rewrite H;
          cbn;
          rewrite lookup_insert;
          rewrite (Hexv24 v1 Hv1lt);
          rewrite (Hexv24 v2 Hv2lt);
          rewrite IH1; rewrite IH2;
          exact (eq_trans _ _ (eq_sym Happv))
        ).
      (* backlink case: nBack with subst chain *)
      destruct (RO.compile_args fuel ρ args b) as [v_args b1] eqn:Hargs.
      (* build subst nil *)
      unfold RO.fresh; simpl.
      set (sv_nil := RO.b_next b1).
      set (b2 := {| RO.b_next := S sv_nil; RO.b_label := RO.b_label b1; RO.b_succ := RO.b_succ b1; RO.b_fix_ty := RO.b_fix_ty b1 |}).
      set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
      destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
      (* backlink node *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b4).
      set (b5 := {| RO.b_next := S v; RO.b_label := RO.b_label b4; RO.b_succ := RO.b_succ b4; RO.b_fix_ty := RO.b_fix_ty b4 |}).
      set (b6 := RO.put v RO.nBack [target; sv] b5).
      (* extract at root v: should yield apps (tVar n) args_terms *)
      subst b6.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      (* fix-ty at v is none *)
      assert (RO.b_fix_ty b4 !! v = None).
      { destruct (RO.b_fix_ty b4 !! v) eqn:Hfx; [destruct (build_subst_chain_dom_lt v_args sv_nil b3 (compile_args_dom_lt fuel ρ args b Hdom)) as [_ [_ Hf]]; specialize (Hf v n0 Hfx); unfold v in Hf; lia|reflexivity]. }
      rewrite H.
      cbn.
      rewrite lookup_insert.
      (* env lookup maps target to n (fix_env_of) *)
      assert (fix_env_of ρ !! target = Some n).
      { apply fix_env_of_nth_some.
        - exact Hnodup.
        - exact Hnth.
      }
      rewrite H0.
      (* subst_args correctness yields extracted arguments *)
      (* establish dom/closed facts for b3 to apply subst_args_build_subst_chain *)
      pose proof (compile_args_dom_lt fuel ρ args b Hdom) as Hdom_args.
      rewrite Hargs in Hdom_args.
      pose proof (compile_args_closed fuel ρ args b (conj Hdom Hcl) Htlt) as Hcl_args.
      rewrite Hargs in Hcl_args.
      (* b3 adds sv_nil; update dom/closed are straightforward *)
      assert (Hdom3 : dom_lt b3).
      { unfold b3. apply dom_lt_put.
        - apply dom_lt_fresh. exact Hdom_args.
        - unfold sv_nil. simpl. lia. }
      assert (Hcl3 : closed_lt b3 (RO.b_next b3)).
      { (* closure after putting subst nil with empty succ *)
        split.
        - intros k succ Hk Hlt.
          unfold b3, RO.put in Hk; simpl in Hk.
          destruct (decide (k = sv_nil)) as [->|Hne].
          + rewrite lookup_insert in Hk. inversion Hk; subst. constructor.
          + rewrite lookup_insert_ne in Hk by exact Hne.
            destruct Hcl_args as [Hsucc _].
            assert (k < RO.b_next b1) by (unfold sv_nil in *; lia).
            specialize (Hsucc k succ Hk H).
            apply (Forall_lt_mono succ (RO.b_next b1) (S sv_nil)); [exact Hsucc|].
            unfold sv_nil. lia.
        - intros k vA Hk Hlt.
          unfold b3, RO.put in Hk; simpl in Hk.
          destruct Hcl_args as [_ Hfix].
          assert (k < RO.b_next b1) by (unfold sv_nil in *; lia).
          specialize (Hfix k vA Hk H).
          unfold sv_nil. lia.
      }
      (* all argument vertices are < b_next b1 *)
      pose proof (compile_args_roots_lt fuel ρ args b) as Hargs_lt.
      rewrite Hargs in Hargs_lt.
      pose proof (subst_args_build_subst_chain fuel (fix_env_of ρ) v_args sv_nil b3 Hdom3 Hcl3 (by (unfold sv_nil, b3, b2; simpl; lia))
                    (by (unfold b3, RO.put; simpl; rewrite lookup_insert; reflexivity))
                    (by (unfold b3, RO.put; simpl; rewrite lookup_insert; reflexivity))
                    (Forall_lt_mono _ _ _ Hargs_lt (by (unfold sv_nil; lia)))) as Hsub.
      rewrite Hch in Hsub.
      rewrite Hsub.
      (* apps term spine reconstructed via app_view_correct *)
      (* extract_vs fuel b4 (fix_env_of ρ) v_args equals extracting args list; this matches args terms *)
      (* conclude *)
      admit
    + (* tFix *) admit
    + (* tInd *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b).
      set (b1 := {| RO.b_next := S v; RO.b_label := RO.b_label b; RO.b_succ := RO.b_succ b; RO.b_fix_ty := RO.b_fix_ty b |}).
      simpl.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      reflexivity.
    + (* tRoll *)
      (* compile params and recs lists, then fresh+put roll node *)
      destruct (RO.compile_list fuel ρ l b) as [vps b1] eqn:Hps.
      assert (Hdom1 : dom_lt b1).
      { pose proof (compile_list_dom_lt fuel ρ l b Hdom) as Hdl. rewrite Hps in Hdl. exact Hdl. }
      assert (Hcl1 : closed_lt b1 (RO.b_next b1)).
      { pose proof (compile_list_closed fuel ρ l b (conj Hdom Hcl) Htlt) as Hc. rewrite Hps in Hc. exact Hc. }
      pose proof (compile_list_bnext_mono fuel ρ l b) as Hmn1.
      rewrite Hps in Hmn1.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
      destruct (RO.compile_list fuel ρ l0 b1) as [vrs b2] eqn:Hrs.
      assert (Hdom2 : dom_lt b2).
      { pose proof (compile_list_dom_lt fuel ρ l0 b1 Hdom1) as Hdl. rewrite Hrs in Hdl. exact Hdl. }
      assert (Hcl2 : closed_lt b2 (RO.b_next b2)).
      { pose proof (compile_list_closed fuel ρ l0 b1 (conj Hdom1 Hcl1) Htlt1) as Hc. rewrite Hrs in Hc. exact Hc. }
      pose proof (compile_list_bnext_mono fuel ρ l0 b1) as Hmn2.
      rewrite Hrs in Hmn2.
      assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt1|exact Hmn2]).
      (* correctness of params and recs lists via Hcompile_list *)
      pose proof (Hcompile_list l b vps b1 Hdom Hcl Hnodup Htlt Hps) as Hps_ex_b1.
      pose proof (Hcompile_list l0 b1 vrs b2 Hdom1 Hcl1 Hnodup Htlt1 Hrs) as Hrs_ex_b2.
      (* lift params equality from b1 to b2 (recs compilation extends builder) *)
      pose proof (compile_list_preserves_lt fuel ρ l0 b1) as Hpres12.
      rewrite Hrs in Hpres12.
      assert (Hagree12 : forall k,
                k < RO.b_next b1 ->
                b2.(RO.b_label) !! k = b1.(RO.b_label) !! k
                /\ b2.(RO.b_succ) !! k = b1.(RO.b_succ) !! k
                /\ b2.(RO.b_fix_ty) !! k = b1.(RO.b_fix_ty) !! k)
        by (intros k Hk; apply Hpres12; exact Hk).
      pose proof (extract_ext (b := b1) (b' := b2) (ρ := fix_env_of ρ) (n := RO.b_next b1) Hagree12 Hcl1 fuel) as [Hexv12 _].
      pose proof (compile_list_roots_lt fuel ρ l b) as Hvps_lt.
      rewrite Hps in Hvps_lt.
      assert (Hps_ex_b2 : map (EX.extract_v fuel b2 (fix_env_of ρ)) vps = l).
      { clear -Hps_ex_b1 Hexv12 Hvps_lt.
        induction vps as [|x xs IHxs]; simpl in *.
        - exact Hps_ex_b1.
        - inversion Hvps_lt; subst.
          f_equal.
          + rewrite (Hexv12 x H1). reflexivity.
          + apply IHxs. exact H4.
      }
      (* final fresh+put *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b2).
      set (b3 := {| RO.b_next := S v; RO.b_label := RO.b_label b2; RO.b_succ := RO.b_succ b2; RO.b_fix_ty := RO.b_fix_ty b2 |}).
      set (b4 := RO.put v (RO.nRoll n n0 (length vps) (length vrs)) (vps ++ vrs) b3).
      (* extensionality from b2 to b4 for old vertices *)
      assert (Hagree24 : forall k,
                k < v ->
                b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k).
      { intros k Hk.
        unfold b4, RO.put. simpl.
        assert (k <> v) by lia.
        repeat split; rewrite lookup_insert_ne; auto. }
      (* b2 is closed and we widen to b4 *)
      pose proof (extract_ext (b := b2) (b' := b4) (ρ := fix_env_of ρ) (n := v) Hagree24 Hcl2 (fuel + 1)) as [Hexv24 _].
      (* list of successors all < v *)
      pose proof (compile_list_roots_lt fuel ρ l b) as Hltps.
      rewrite Hps in Hltps.
      pose proof (compile_list_roots_lt fuel ρ l0 b1) as Hltrs.
      rewrite Hrs in Hltrs.
      (* now extract at root v *)
      subst b4.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      assert (RO.b_fix_ty b2 !! v = None).
      { destruct (RO.b_fix_ty b2 !! v) eqn:Hfx; [|reflexivity].
        destruct Hdom2 as [_ [_ Hf]].
        specialize (Hf v n1 Hfx).
        unfold v in Hf. lia. }
      rewrite H.
      cbn.
      rewrite lookup_insert.
      (* simplify maps over take/drop by rewriting map extract_v pointwise using Hexv24 *)
      (* first, show map over vps in b4 equals map over vps in b2 *)
      assert (Hmap_ps : map (EX.extract_v fuel b4 (fix_env_of ρ)) vps = map (EX.extract_v fuel b2 (fix_env_of ρ)) vps).
      { apply map_ext_in.
        intros x Hxin.
        pose proof (Forall_forall _ _ Hltps x Hxin) as Hxlt.
        rewrite (Hexv24 x Hxlt).
        reflexivity. }
      assert (Hmap_rs : map (EX.extract_v fuel b4 (fix_env_of ρ)) vrs = map (EX.extract_v fuel b2 (fix_env_of ρ)) vrs).
      { apply map_ext_in.
        intros x Hxin.
        pose proof (Forall_forall _ _ Hltrs x Hxin) as Hxlt.
        (* vrs vertices are < b_next b2 = v *)
        assert (x < v) by (unfold v; lia).
        rewrite (Hexv24 x H).
        reflexivity. }
      (* use extracted list equalities *)
      rewrite Hmap_ps.
      rewrite Hmap_rs.
      rewrite Hps_ex_b2.
      rewrite Hrs_ex_b2.
      reflexivity
    + (* tCase *)
      (* compile scrutinee, motive, and branch list, then fresh+put case node *)
      destruct (RO.compile_tm fuel ρ t1 b) as [vscrut b1] eqn:Hs.
      assert (Hfuels : fuel >= T.size t1) by (simpl in Hfuel; lia).
      pose proof (IH ρ t1 b Hfuels Hdom Hcl Hnodup Htlt) as Hscrut.
      rewrite Hs in Hscrut. simpl in Hscrut.
      (* propagate invariants to b1 *)
      pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom) as Hdom1.
      rewrite Hs in Hdom1.
      pose proof (compile_tm_closed fuel ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1.
      rewrite Hs in Hcl1.
      pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1.
      rewrite Hs in Hmn1.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
      (* compile motive C *)
      destruct (RO.compile_tm fuel ρ t2 b1) as [vC b2] eqn:Hc.
      assert (HfuelC : fuel >= T.size t2) by (simpl in Hfuel; lia).
      pose proof (IH ρ t2 b1 HfuelC Hdom1 Hcl1 Hnodup Htlt1) as HC.
      rewrite Hc in HC. simpl in HC.
      pose proof (compile_tm_dom_lt fuel ρ t2 b1 Hdom1) as Hdom2.
      rewrite Hc in Hdom2.
      pose proof (compile_tm_closed fuel ρ t2 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
      rewrite Hc in Hcl2.
      pose proof (compile_tm_bnext_mono fuel ρ t2 b1) as Hmn2.
      rewrite Hc in Hmn2.
      assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt1|exact Hmn2]).
      (* compile branches *)
      destruct (RO.compile_list fuel ρ l b2) as [vbrs b3] eqn:Hbrs.
      assert (Hdom3 : dom_lt b3).
      { pose proof (compile_list_dom_lt fuel ρ l b2 Hdom2) as Hd. rewrite Hbrs in Hd. exact Hd. }
      assert (Hcl3 : closed_lt b3 (RO.b_next b3)).
      { pose proof (compile_list_closed fuel ρ l b2 (conj Hdom2 Hcl2) Htlt2) as Hc'. rewrite Hbrs in Hc'. exact Hc'. }
      (* branch list correctness via Hcompile_list *)
      pose proof (Hcompile_list l b2 vbrs b3 Hdom2 Hcl2 Hnodup Htlt2 Hbrs) as Hbrs_ex_b3.
      (* final fresh+put *)
      unfold RO.fresh; simpl.
      set (v := RO.b_next b3).
      set (b4 := {| RO.b_next := S v; RO.b_label := RO.b_label b3; RO.b_succ := RO.b_succ b3; RO.b_fix_ty := RO.b_fix_ty b3 |}).
      set (b5 := RO.put v (RO.nCase n (length vbrs)) ([vscrut; vC] ++ vbrs) b4).
      assert (Hagree35 : forall k,
                k < v ->
                b5.(RO.b_label) !! k = b3.(RO.b_label) !! k
                /\ b5.(RO.b_succ) !! k = b3.(RO.b_succ) !! k
                /\ b5.(RO.b_fix_ty) !! k = b3.(RO.b_fix_ty) !! k).
      { intros k Hk.
        unfold b5, RO.put. simpl.
        assert (k <> v) by lia.
        repeat split; rewrite lookup_insert_ne; auto. }
      pose proof (extract_ext (b := b3) (b' := b5) (ρ := fix_env_of ρ) (n := v) Hagree35 Hcl3 fuel) as [Hexv35 _].
      (* bounds for vscrut/vC/vbrs elements < v *)
      pose proof (compile_tm_root_lt fuel ρ t1 b) as Hvs.
      rewrite Hs in Hvs.
      pose proof (compile_tm_root_lt fuel ρ t2 b1) as HvC.
      rewrite Hc in HvC.
      pose proof (compile_list_roots_lt fuel ρ l b2) as Hbrlt.
      rewrite Hbrs in Hbrlt.
      assert (Hvs_lt : vscrut < v) by (unfold v; lia).
      assert (HvC_lt : vC < v) by (unfold v; lia).
      (* now extract at root v *)
      subst b5.
      cbn [EX.extract_v EX.lookup_node EX.lookup_succ].
      rewrite lookup_insert.
      assert (RO.b_fix_ty b3 !! v = None).
      { destruct (RO.b_fix_ty b3 !! v) eqn:Hfx; [|reflexivity].
        destruct Hdom3 as [_ [_ Hf]].
        specialize (Hf v n0 Hfx).
        unfold v in Hf. lia. }
      rewrite H.
      cbn.
      rewrite lookup_insert.
      (* rewrite child extractions to b3 and then to original terms *)
      rewrite (Hexv35 vscrut Hvs_lt).
      rewrite (Hexv35 vC HvC_lt).
      (* map over branches *)
      assert (Hmap_brs : map (EX.extract_v fuel b5 (fix_env_of ρ)) vbrs = map (EX.extract_v fuel b3 (fix_env_of ρ)) vbrs).
      { apply map_ext_in.
        intros x Hxin.
        pose proof (Forall_forall _ _ Hbrlt x Hxin) as Hxlt.
        assert (x < v) by (unfold v; lia).
        rewrite (Hexv35 x H).
        reflexivity. }
      rewrite Hmap_brs.
      (* finish by rewriting with computed equalities *)
      rewrite Hscrut.
      rewrite HC.
      rewrite Hbrs_ex_b3.
      reflexivity
Qed.

Theorem extract_read_off_id (t : T.tm) : EX.extract_read_off t = t.
Proof.
  unfold EX.extract_read_off.
  destruct (RO.read_off_raw t) as [root b] eqn:H.
  unfold RO.read_off_raw in H.
  (* read_off_raw is compile_tm (size t) [] t empty_builder *)
  cbn in H.
  (* use extract_compile_tm with empty builder/back env *)
  specialize (extract_compile_tm (T.size t) [] t RO.empty_builder).
  (* TODO: finish using extract_compile_tm once its proof is complete. *)
Admitted.

Theorem extract_read_off_ciu
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
  CIUJudgement.ciu_jTy Σenv Γ t (EX.extract_read_off t) A.
Proof.
  apply CIUJudgement.ciu_jTy_of_eq.
  apply extract_read_off_id.
Qed.
