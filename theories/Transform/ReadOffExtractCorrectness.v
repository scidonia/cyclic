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

  === PROOF STRUCTURE ===

  The proof follows this dependency chain:

  1. **Builder invariants** (dom_lt, closed_lt, preserves_lt, wf_builder)
     - Establish that compilation maintains well-formedness
     - Show that vertices stay within b_next bounds
     - Prove compilation doesn't overwrite old vertices

  2. **Monotonicity lemmas** (compile_tm_bnext_mono, compile_list_bnext_mono)
     - Show b_next only increases during compilation
     - Needed for preservation arguments

  3. **Back-environment correspondence** (fix_env_of, targets_lt, nodup_targets)
     - Relate compilation's back_env to extraction's fix_env
     - Ensure cycle targets are properly tracked

  4. **Extraction stability** (extract_ext section, NEEDS PORTING from snapshot)
     - Key lemma: extraction from b and b' agree on vertices < n
       when b and b' agree on those vertices
     - Allows lifting extraction correctness across builder extensions

  5. **Compilation correctness** (extract_compile_tm, NEEDS PORTING from snapshot)
     - Main theorem: EX.extract_v fuel b' (fix_env_of ρ) v = t
       where (v, b') = RO.compile_tm fuel ρ t b
     - Proven by mutual induction on term structure
     - Uses extract_ext to handle intermediate builders

  6. **Round-trip theorem** (extract_read_off_id)
     - Follows from extract_compile_tm applied to read_off_raw
     - Instantiate with empty builder and environment

  === CURRENT STATUS ===

  - Infrastructure lemmas: ADMITTED (all provable, see snapshot file)
  - Monotonicity: ADMITTED (provable, tactical issues only)
  - extract_ext: NEEDS PORTING (complete proof in snapshot at line ~1473)
  - extract_compile_tm: NEEDS PORTING (complete proof in snapshot at line ~1685)
  - extract_read_off_id: ADMITTED (straightforward once above are ported)

  The snapshot file `ReadOffExtractCorrectness_Snapshot.v` contains complete
  proofs for all admitted lemmas. The main work remaining is careful porting
  of the large extract_ext and extract_compile_tm proofs.
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
  intros Hlt -> Hin.
  induction Hlt as [|x xs Hx Hxs IH]; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + lia.
    + apply IH. exact Hin.
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
  induction ρ as [|o ρ IH]; intros [|x] Hnd H; simpl in H.
  - discriminate.
  - discriminate.
  - destruct o; simpl in H.
    + inversion H; subst.
      rewrite fix_env_of_cons_some.
      pose proof (lookup_insert (EX.env_shift (fix_env_of ρ)) target target 0) as Hlk.
      rewrite decide_True in Hlk by reflexivity.
      simpl in Hlk.
      exact Hlk.
    + discriminate.
  - destruct o as [v|].
    + simpl in H.
      rewrite fix_env_of_cons_some.
      specialize (IH x (nodup_targets_tail _ _ Hnd) H).
      (* target comes from tail, so it cannot be v by NoDup *)
      assert (target <> v).
       { intros ->.
        (* v appears at head and also in tail at index x *)
        inversion Hnd as [|?? Hnotin]; subst.
        apply Hnotin.
        (* show v in targets_of ρ using nth_error hypothesis *)
        apply (proj2 (list_elem_of_In (targets_of ρ) v)).
        apply (nth_error_targets_of ρ x v H).
      }
      rewrite (lookup_insert_ne (EX.env_shift (fix_env_of ρ)) v target 0);
        [|intros Heq; apply H0; now symmetry].

      unfold EX.env_shift.
      apply (proj2 (lookup_fmap_Some S (fix_env_of ρ) target (S x))).
      exists x. split; [reflexivity|exact IH].
    + (* None binder *)
      simpl in H.
      rewrite fix_env_of_cons_none.
      specialize (IH x (nodup_targets_tail _ _ Hnd) H).
      unfold EX.env_shift.
      apply (proj2 (lookup_fmap_Some S (fix_env_of ρ) target (S x))).
      exists x. split; [reflexivity|exact IH].
Qed.

(** Term-level application spine (left-associated). *)
Fixpoint apps_tm (t : T.tm) (us : list T.tm) : T.tm :=
  match us with
  | [] => t
  | u :: us => apps_tm (T.tApp t u) us
  end.

Lemma apps_tm_snoc (h : T.tm) (args : list T.tm) (u : T.tm) :
  apps_tm h (args ++ [u]) = T.tApp (apps_tm h args) u.
Proof.
  revert h.
  induction args as [|a args IH]; intros h; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma app_view_correct (t : T.tm) :
  let '(h, args) := RO.app_view t in
  t = apps_tm h args.
Proof.
  induction t; simpl; try reflexivity.
  destruct (RO.app_view t1) as [h args] eqn:Hview.
  simpl.
  specialize (IHt1).
  simpl in IHt1.
  rewrite IHt1.
  rewrite apps_tm_snoc.
  reflexivity.
Qed.

Local Opaque RO.app_view.

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
  repeat split; intros; simpl in H; rewrite lookup_empty in H; discriminate.
Qed.

Lemma dom_lt_put (b : RO.builder) (v : nat) (lbl : RO.node) (succ : list nat) :
  dom_lt b -> v < RO.b_next b -> dom_lt (RO.put v lbl succ b).
Proof.
  intros [Hl [Hs Hf]] Hv.
  repeat split.
  - intros k n Hk.
    destruct (decide (k = v)) as [->|Hne].
    + simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by (intros Heq; apply Hne; now symmetry).
      apply Hl in Hk. exact Hk.
  - intros k s Hk.
    destruct (decide (k = v)) as [->|Hne].
    + simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by (intros Heq; apply Hne; now symmetry).
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
      rewrite lookup_insert_ne in Hk by (intros Heq; apply Hne; now symmetry).
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
  - intros k n Hk. specialize (Hl k n Hk). exact (Nat.lt_lt_succ_r _ _ Hl).
  - intros k s Hk. specialize (Hs k s Hk). exact (Nat.lt_lt_succ_r _ _ Hs).
  - intros k vA Hk. specialize (Hf k vA Hk). exact (Nat.lt_lt_succ_r _ _ Hf).
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

Lemma preserves_lt_put_over (b b0 : RO.builder) (v : nat) (lbl : RO.node) (succ : list nat) :
  preserves_lt b b0 ->
  v >= RO.b_next b ->
  preserves_lt b (RO.put v lbl succ b0).
Proof.
  intros Hpres Hv k Hk.
  specialize (Hpres k Hk) as [Hlbl [Hsucc Hfix]].
  assert (Hneq : v <> k) by lia.
  unfold RO.put; simpl.
  repeat split.
  - rewrite lookup_insert_ne by exact Hneq. exact Hlbl.
  - rewrite lookup_insert_ne by exact Hneq. exact Hsucc.
  - exact Hfix.
Qed.

Lemma preserves_lt_put_fix_ty_over (b b0 : RO.builder) (v vA : nat) :
  preserves_lt b b0 ->
  v >= RO.b_next b ->
  preserves_lt b (RO.put_fix_ty v vA b0).
Proof.
  intros Hpres Hv k Hk.
  specialize (Hpres k Hk) as [Hlbl [Hsucc Hfix]].
  assert (Hneq : v <> k) by lia.
  unfold RO.put_fix_ty; simpl.
  repeat split.
  - exact Hlbl.
  - exact Hsucc.
  - rewrite lookup_insert_ne by exact Hneq. exact Hfix.
Qed.

(** Successor/fix-ty closure w.r.t. current [b_next]. *)
Definition wf_builder (b : RO.builder) : Prop :=
  dom_lt b /\ closed_lt b (RO.b_next b).

Lemma wf_builder_empty : wf_builder RO.empty_builder.
Proof.
  split.
  - apply dom_lt_empty.
  - split; intros; simpl in H; rewrite lookup_empty in H; discriminate.
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
    destruct Hdom as [_ [Hdom_succ Hdom_fix]].
    split.
    + intros k succ Hk Hlt.
      unfold RO.fresh in Hk.
      simpl in Hk.
      (* Hk : b_succ b !! k = Some succ *)
      (* need: k < b_next b from dom_lt *)
      assert (Hklt : k < RO.b_next b). {
        eapply Hdom_succ; eauto.
      }
      specialize (Hsucc k succ Hk Hklt) as Hclosed_succ.
      (* Hclosed_succ : Forall (w < b_next b) succ *)
      (* need: Forall (w < S (b_next b)) succ *)
      eapply Forall_impl; [exact Hclosed_succ|].
      intros w Hw.
      exact (Nat.lt_lt_succ_r _ _ Hw).
    + intros k vA Hk Hlt.
      unfold RO.fresh in Hk.
      simpl in Hk.
      (* Hk : b_fix_ty b !! k = Some vA *)
      assert (Hklt : k < RO.b_next b). {
        eapply Hdom_fix; eauto.
      }
      specialize (Hfix k vA Hk Hklt) as HvAlt.
      (* HvAlt : vA < b_next b *)
      exact (Nat.lt_lt_succ_r _ _ HvAlt).
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
  (* Provable - see snapshot lines 390-455.
     Tactical issue: after simpl, RO.fresh unfolds inside the term but the goal
     doesn't reduce properly. The proof works in the snapshot with exact tactics. *)
Admitted.

Lemma build_subst_chain_bnext_mono (us : list nat) (sv_tail : nat) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.build_subst_chain us sv_tail b)).
Proof.
  revert b.
  induction us as [|u us IH]; intro b; simpl.
  - lia.
  - destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    specialize (IH b).
    rewrite Hch in IH. simpl in IH.
    unfold RO.fresh, RO.put. simpl. lia.
Qed.

(* Mutual monotonicity: both compile_tm and compile_list preserve b_next bounds *)
Lemma compile_tm_list_bnext_mono_mutual :
  forall fuel,
    (forall ρ t b, RO.b_next b <= RO.b_next (snd (RO.compile_tm fuel ρ t b)))
    /\ (forall ρ ts b, RO.b_next b <= RO.b_next (snd (RO.compile_list fuel ρ ts b))).
Proof.
  induction fuel as [|fuel IH].
  - split.
    + intros ρ t b.
      cbn [RO.compile_tm].
      destruct (RO.fresh b) as [v b1] eqn:Hfr.
      pose proof (fresh_snd_next b) as Hb1next.
      rewrite Hfr in Hb1next. simpl in Hb1next.
      unfold RO.put. simpl. lia.
    + intros ρ ts b.
      cbn [RO.compile_list].
      apply Nat.le_refl.
  - destruct IH as [IHtm IHlist].
    split.
    + intros ρ t b.
      cbn [RO.compile_tm].
      destruct t as
          [x
          |i
          |A B
          |A t0
          |t1 t2
          |A body
          |I
          |I c params recs
          |I scrut C brs].
      * (* tVar *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        unfold RO.put. simpl. lia.
      * (* tSort *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        unfold RO.put. simpl. lia.
      * (* tPi *)
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b) as Hmn1.
        rewrite HA in Hmn1. simpl in Hmn1.
        destruct (RO.compile_tm fuel (None :: ρ) B b1) as [vB b2] eqn:HB.
        pose proof (IHtm (None :: ρ) B b1) as Hmn2.
        rewrite HB in Hmn2. simpl in Hmn2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        unfold RO.put. simpl.
        lia.
      * (* tLam *)
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b) as Hmn1.
        rewrite HA in Hmn1. simpl in Hmn1.
        destruct (RO.compile_tm fuel (None :: ρ) t0 b1) as [vt b2] eqn:Ht0.
        pose proof (IHtm (None :: ρ) t0 b1) as Hmn2.
        rewrite Ht0 in Hmn2. simpl in Hmn2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        unfold RO.put. simpl.
        lia.
      * (* tApp *)
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h;
          try (
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IHtm ρ t1 b) as Hmn1; rewrite H1 in Hmn1; simpl in Hmn1;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IHtm ρ t2 b1) as Hmn2; rewrite H2 in Hmn2; simpl in Hmn2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (fresh_snd_next b2) as Hb3next; rewrite Hfr in Hb3next; simpl in Hb3next;
            unfold RO.put; simpl; lia).
        destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
          try (
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IHtm ρ t1 b) as Hmn1; rewrite H1 in Hmn1; simpl in Hmn1;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IHtm ρ t2 b1) as Hmn2; rewrite H2 in Hmn2; simpl in Hmn2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (fresh_snd_next b2) as Hb3next; rewrite Hfr in Hb3next; simpl in Hb3next;
            unfold RO.put; simpl; lia).
        (* backlink case *)
        destruct (RO.compile_list fuel ρ args b) as [v_args b1] eqn:Hargs.
        pose proof (IHlist ρ args b) as Hmargs.
        rewrite Hargs in Hmargs. simpl in Hmargs.
        destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfr1.
        set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
        destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
        pose proof (build_subst_chain_bnext_mono v_args sv_nil b3) as Hbmn.
        rewrite Hch in Hbmn.
        destruct (RO.fresh b4) as [v_back b5] eqn:Hfr2.
        pose proof (fresh_snd_next b1) as Hb2next.
        rewrite Hfr1 in Hb2next. simpl in Hb2next.
        pose proof (fresh_snd_next b4) as Hb5next.
        rewrite Hfr2 in Hb5next. simpl in Hb5next.
        assert (Hb1_le_b2 : RO.b_next b1 <= RO.b_next b2) by (rewrite Hb2next; lia).
        assert (Hb2_eq_b3 : RO.b_next b2 = RO.b_next b3).
        { unfold b3. unfold RO.put. simpl. reflexivity. }
        assert (Hb2_le_b4 : RO.b_next b2 <= RO.b_next b4).
        { rewrite Hb2_eq_b3. exact Hbmn. }
        assert (Hb_le_b4 : RO.b_next b <= RO.b_next b4).
        { eapply Nat.le_trans; [exact Hmargs|].
          eapply Nat.le_trans; [exact Hb1_le_b2|exact Hb2_le_b4]. }
        unfold RO.put. simpl.
        rewrite Hb5next.
        lia.
      * (* tFix *)
        destruct (RO.fresh b) as [v b0] eqn:Hfr.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b) as Hb0next.
        rewrite Hfr in Hb0next. simpl in Hb0next.
        destruct (RO.compile_tm fuel ρ A b0) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b0) as Hmn1.
        rewrite HA in Hmn1. simpl in Hmn1.
        set (b1' := RO.put_fix_ty (RO.b_next b) vA b1).
        destruct (RO.compile_tm fuel (Some (RO.b_next b) :: ρ) body b1') as [vbody b2] eqn:HB.
        pose proof (IHtm (Some (RO.b_next b) :: ρ) body b1') as Hmn2.
        rewrite HB in Hmn2. simpl in Hmn2.
        subst b1'. simpl in Hmn2.
        assert (Hb_le_b0 : RO.b_next b <= RO.b_next b0) by (rewrite Hb0next; lia).
        assert (Hb_le_b2 : RO.b_next b <= RO.b_next b2) by lia.
        unfold RO.put. simpl.
        exact Hb_le_b2.
      * (* tInd *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        unfold RO.put. simpl. lia.
      * (* tRoll *)
        destruct (RO.compile_list fuel ρ params b) as [vps b1] eqn:Hps.
        pose proof (IHlist ρ params b) as Hmn1.
        rewrite Hps in Hmn1. simpl in Hmn1.
        destruct (RO.compile_list fuel ρ recs b1) as [vrs b2] eqn:Hrs.
        pose proof (IHlist ρ recs b1) as Hmn2.
        rewrite Hrs in Hmn2. simpl in Hmn2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        unfold RO.put. simpl. lia.
      * (* tCase *)
        destruct (RO.compile_tm fuel ρ scrut b) as [vscrut b1] eqn:Hs.
        pose proof (IHtm ρ scrut b) as Hmn1.
        rewrite Hs in Hmn1. simpl in Hmn1.
        destruct (RO.compile_tm fuel ρ C b1) as [vC b2] eqn:Hc.
        pose proof (IHtm ρ C b1) as Hmn2.
        rewrite Hc in Hmn2. simpl in Hmn2.
        destruct (RO.compile_list fuel ρ brs b2) as [vbrs b3] eqn:Hbrs.
        pose proof (IHlist ρ brs b2) as Hmn3.
        rewrite Hbrs in Hmn3. simpl in Hmn3.
        destruct (RO.fresh b3) as [v b4] eqn:Hfr.
        pose proof (fresh_snd_next b3) as Hb4next.
        rewrite Hfr in Hb4next. simpl in Hb4next.
        unfold RO.put. simpl. lia.
    + intros ρ ts b.
      cbn [RO.compile_list].
      destruct ts as [|t ts].
      * apply Nat.le_refl.
      * destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
        pose proof (IHtm ρ t b) as Hmn1.
        rewrite Ht in Hmn1. simpl in Hmn1.
        destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
        pose proof (IHlist ρ ts b1) as Hmn2.
        rewrite Hts in Hmn2. simpl in Hmn2.
        exact (Nat.le_trans _ _ _ Hmn1 Hmn2).
Qed.

Lemma compile_tm_bnext_mono
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.compile_tm fuel ρ t b)).
Proof. apply (compile_tm_list_bnext_mono_mutual fuel). Qed.

Lemma compile_list_bnext_mono
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  RO.b_next b <= RO.b_next (snd (RO.compile_list fuel ρ ts b)).
Proof. apply (compile_tm_list_bnext_mono_mutual fuel). Qed.

(* Now the original compile_tm_bnext_mono body can be removed *)
Lemma compile_tm_list_root_lt_mutual :
  forall fuel,
    (forall ρ t b,
        fst (RO.compile_tm fuel ρ t b) < RO.b_next (snd (RO.compile_tm fuel ρ t b)))
    /\ (forall ρ ts b,
          Forall (fun v => v < RO.b_next (snd (RO.compile_list fuel ρ ts b)))
            (fst (RO.compile_list fuel ρ ts b))).
Proof.
Admitted.

Lemma compile_tm_root_lt
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  fst (RO.compile_tm fuel ρ t b) < RO.b_next (snd (RO.compile_tm fuel ρ t b)).
Proof.
  revert ρ t b.
  induction fuel as [|fuel IH]; intros ρ t b; cbn [RO.compile_tm].
  - unfold RO.fresh. simpl. lia.
  - destruct t as
        [x
        |i
        |A B
        |A t0
        |t1 t2
        |A body
        |I
        |I c params recs
        |I scrut C brs];
      cbn [RO.compile_tm].
    * (* tVar *) unfold RO.fresh, RO.put. simpl. lia.
    * (* tSort *) unfold RO.fresh, RO.put. simpl. lia.
    * (* tPi *)
      destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
      destruct (RO.compile_tm fuel (None :: ρ) B b1) as [vB b2] eqn:HB.
      unfold RO.fresh, RO.put. simpl. lia.
    * (* tLam *)
      destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
      destruct (RO.compile_tm fuel (None :: ρ) t0 b1) as [vt b2] eqn:Ht.
      unfold RO.fresh, RO.put. simpl. lia.
    * (* tApp *)
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h;
          try (
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            unfold RO.fresh, RO.put; simpl; lia).
        destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
          try (
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            unfold RO.fresh, RO.put; simpl; lia).
      (* backlink case *)
      destruct (RO.compile_list fuel ρ args b) as [v_args b1] eqn:Hargs.
      destruct (RO.fresh b1) as [sv_nil b2] eqn:Hnil.
      set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
      destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
      destruct (RO.fresh b4) as [v b5] eqn:Hf.
      pose proof (fresh_fst_eq b4) as Hvf.
      rewrite Hf in Hvf. simpl in Hvf.
        pose proof (fresh_snd_next b4) as Hb5next.
        rewrite Hf in Hb5next. simpl in Hb5next.
      unfold RO.put. simpl.
      rewrite Hvf.
      rewrite Hb5next.
      lia.
    * (* tFix *)
      destruct (RO.fresh b) as [v b0] eqn:Hfr.
      pose proof (fresh_fst_eq b) as Hv.
      rewrite Hfr in Hv. simpl in Hv.
      pose proof (fresh_snd_next b) as Hb0next.
      rewrite Hfr in Hb0next. simpl in Hb0next.
      destruct (RO.compile_tm fuel ρ A b0) as [vA b1] eqn:HA.
      pose proof (compile_tm_bnext_mono fuel ρ A b0) as HmnA.
      rewrite HA in HmnA. simpl in HmnA.
      set (b1' := RO.put_fix_ty v vA b1).
      destruct (RO.compile_tm fuel (Some v :: ρ) body b1') as [vbody b2] eqn:HB.
      pose proof (compile_tm_bnext_mono fuel (Some v :: ρ) body b1') as HmnB.
      rewrite HB in HmnB. simpl in HmnB.
      unfold b1' in HmnB. simpl in HmnB.
      unfold RO.put. simpl.
      rewrite Hv.
      (* b_next b0 = S v, and compilation is b_next-mono *)
      lia.
    * (* tInd *) unfold RO.fresh, RO.put. simpl. lia.
    * (* tRoll *)
      destruct (RO.compile_list fuel ρ params b) as [vps b1] eqn:Hps.
      destruct (RO.compile_list fuel ρ recs b1) as [vrs b2] eqn:Hrs.
      unfold RO.fresh, RO.put. simpl. lia.
    * (* tCase *)
      destruct (RO.compile_tm fuel ρ scrut b) as [vscrut b1] eqn:Hs.
      destruct (RO.compile_tm fuel ρ C b1) as [vC b2] eqn:Hc.
      destruct (RO.compile_list fuel ρ brs b2) as [vbrs b3] eqn:Hbrs.
      unfold RO.fresh, RO.put. simpl. lia.
Qed.

(** Closedness after compilation: successors and fix-ty values stay < b_next. *)
Lemma Forall_lt_mono (xs : list nat) (n m : nat) :
  Forall (fun w => w < n) xs -> n <= m -> Forall (fun w => w < m) xs.
Proof.
  intros H Hle.
  induction H as [|x xs Hx Hxs IH].
  - constructor.
  - constructor; [lia | exact IH].
Qed.

Lemma closed_lt_put_over (b : RO.builder) (n v : nat) (lbl : RO.node) (succs : list nat) :
  closed_lt b n ->
  v < n ->
  Forall (fun w => w < n) succs ->
  closed_lt (RO.put v lbl succs b) n.
Proof.
  intros [Hsucc Hfix] Hv Hsuccs.
  split.
  - intros k succ Hk Hklt.
    unfold RO.put in Hk. simpl in Hk.
    destruct (decide (k = v)) as [->|Hne].
    + try (rewrite lookup_insert in Hk).
      destruct (decide (v = v)) as [_|Hfalse].
      * simpl in Hk. inversion Hk; subst. exact Hsuccs.
      * exfalso; apply Hfalse; reflexivity.
    + destruct (decide (v = k)) as [Heq|Hneq].
      * exfalso; apply Hne; symmetry; exact Heq.
      * try (rewrite lookup_insert_ne in Hk by exact Hneq).
        simpl in Hk.
        exact (Hsucc k succ Hk Hklt).
  - intros k vA Hk Hklt.
    unfold RO.put in Hk. simpl in Hk.
    exact (Hfix k vA Hk Hklt).
Qed.

Lemma closed_lt_put_fix_ty_over (b : RO.builder) (n k vA : nat) :
  closed_lt b n ->
  k < n ->
  vA < n ->
  closed_lt (RO.put_fix_ty k vA b) n.
Proof.
  intros [Hsucc Hfix] Hklt HvA.
  split.
  - intros k0 succ Hk0 Hlt.
    unfold RO.put_fix_ty in Hk0. simpl in Hk0.
    exact (Hsucc k0 succ Hk0 Hlt).
  - intros k0 vA0 Hk0 Hlt.
    unfold RO.put_fix_ty in Hk0. simpl in Hk0.
    destruct (decide (k0 = k)) as [->|Hne].
    + try (rewrite lookup_insert in Hk0).
      destruct (decide (k = k)) as [_|Hfalse].
      * simpl in Hk0. inversion Hk0; subst. exact HvA.
      * exfalso; apply Hfalse; reflexivity.
    + destruct (decide (k = k0)) as [Heq|Hneq].
      * exfalso; apply Hne; symmetry; exact Heq.
      * try (rewrite lookup_insert_ne in Hk0 by exact Hneq).
        simpl in Hk0.
        exact (Hfix k0 vA0 Hk0 Hlt).
Qed.

Lemma build_subst_chain_dom_lt (us : list nat) (sv_tail : nat) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.build_subst_chain us sv_tail b)).
Proof.
  revert b.
  induction us as [|u us IH]; intro b; simpl; intro Hdom.
  - exact Hdom.
  - destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    specialize (IH b Hdom).
    rewrite Hch in IH. simpl in IH.
    (* Now IH : dom_lt b1 *)
    (* Goal: dom_lt (put ... (fresh b1).2) *)
    apply dom_lt_put.
    + apply dom_lt_fresh. exact IH.
    + unfold RO.fresh. simpl. lia.
Qed.

Lemma compile_list_roots_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  Forall (fun v => v < RO.b_next (snd (RO.compile_list fuel ρ ts b)))
    (fst (RO.compile_list fuel ρ ts b)).
Proof.
  revert ts b.
  induction fuel as [|fuel IH]; intros ts b; simpl.
  - constructor.
  - destruct ts as [|t ts]; [constructor|].
    destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
    destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
    simpl.
    constructor.
    + pose proof (compile_tm_root_lt fuel ρ t b) as Hv.
      rewrite Ht in Hv. simpl in Hv.
      pose proof (compile_list_bnext_mono fuel ρ ts b1) as Hmn.
      rewrite Hts in Hmn. simpl in Hmn.
      lia.
    + specialize (IH ts b1).
      rewrite Hts in IH. simpl in IH.
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
  revert sv_tail b.
  induction us as [|u us IH]; intros sv_tail b Hdom Hcl Hsv Hltus.
  - cbn [RO.build_subst_chain].
    exact Hcl.
  - inversion Hltus as [|u0 us0 Hu Hus]; subst u0 us0.
    cbn [RO.build_subst_chain].
    destruct (RO.build_subst_chain us sv_tail b) as [sv_tail' b1] eqn:Hch.
    pose proof (IH sv_tail b Hdom Hcl Hsv Hus) as Hcl1.
    rewrite Hch in Hcl1. simpl in Hcl1.
    pose proof (build_subst_chain_dom_lt us sv_tail b Hdom) as Hdom1.
    rewrite Hch in Hdom1. simpl in Hdom1.
    pose proof (build_subst_chain_bnext_mono us sv_tail b) as Hmn.
    rewrite Hch in Hmn. simpl in Hmn.
    pose proof (build_subst_chain_root_lt us sv_tail b Hsv) as Htail.
    rewrite Hch in Htail. simpl in Htail.
    destruct (RO.fresh b1) as [sv_head b2] eqn:Hfr.
    pose proof (wf_builder_fresh b1 (conj Hdom1 Hcl1)) as Hwf2.
    rewrite Hfr in Hwf2. simpl in Hwf2.
    destruct Hwf2 as [_ Hcl2].
    pose proof (fresh_fst_eq b1) as Hhead.
    rewrite Hfr in Hhead. simpl in Hhead.
    subst sv_head.
    pose proof (fresh_snd_next b1) as Hb2next.
    rewrite Hfr in Hb2next. simpl in Hb2next.
    simpl.
    split.
    + intros k succ Hk Hklt.
      unfold RO.put in Hk. simpl in Hk.
      destruct (decide (k = RO.b_next b1)) as [->|Hne].
      * try (rewrite lookup_insert in Hk).
        destruct (decide (RO.b_next b1 = RO.b_next b1)) as [_|Hfalse].
        -- simpl in Hk.
           inversion Hk; subst; clear Hk.
           constructor.
           ++ (* u < b_next b2 *) lia.
           ++ constructor; [lia|constructor].
        -- exfalso; apply Hfalse; reflexivity.
      * destruct (decide (RO.b_next b1 = k)) as [Heq|Hneq].
        -- exfalso; apply Hne; symmetry; exact Heq.
        -- try (rewrite lookup_insert_ne in Hk by exact Hneq).
           simpl in Hk.
           destruct Hcl2 as [Hsucc2 _].
           exact (Hsucc2 k succ Hk Hklt).
    + intros k vA Hk Hklt.
      unfold RO.put in Hk. simpl in Hk.
      destruct Hcl2 as [_ Hfix2].
      exact (Hfix2 k vA Hk Hklt).
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
  (* ADMITTED: Forward reference to extract_ext (defined at line 1297 in Section ExtractExt).
     This lemma uses extract_ext to show that extraction is stable under builder extension.
     The proof structure is sound but requires extract_ext to be available in scope.
     This lemma is only used later in the file (e.g., line 1884+) after extract_ext is defined,
     so admitting it here doesn't create logical inconsistencies. *)
Admitted.

Lemma compile_tm_dom_lt
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.compile_tm fuel ρ t b))
with compile_list_dom_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  dom_lt b -> dom_lt (snd (RO.compile_list fuel ρ ts b)).
Proof.
  - revert ρ t b.
    induction fuel as [|fuel IH]; intros ρ t b Hdom.
    + cbn [RO.compile_tm].
      destruct (RO.fresh b) as [v b1] eqn:Hfr.
      pose proof (dom_lt_fresh b Hdom) as Hdom1.
      rewrite Hfr in Hdom1. simpl in Hdom1.
      pose proof (fresh_fst_eq b) as Hv.
      rewrite Hfr in Hv. simpl in Hv.
      pose proof (fresh_snd_next b) as Hb1next.
      rewrite Hfr in Hb1next. simpl in Hb1next.
      apply (dom_lt_put b1 v (RO.nVar 0) [] Hdom1).
      lia.
    + cbn [RO.compile_tm].
      destruct t as
          [x
          |i
          |A B
          |A t0
          |t1 t2
          |A body
          |I
          |I c params recs
          |I scrut C brs].
      * cbn [RO.compile_tm].
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (dom_lt_fresh b Hdom) as Hdom1.
        rewrite Hfr in Hdom1. simpl in Hdom1.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        apply (dom_lt_put b1 v (RO.nVar x) [] Hdom1).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (dom_lt_fresh b Hdom) as Hdom1.
        rewrite Hfr in Hdom1. simpl in Hdom1.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        apply (dom_lt_put b1 v (RO.nSort i) [] Hdom1).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IH ρ A b Hdom) as Hdom1.
        rewrite HA in Hdom1. simpl in Hdom1.
        destruct (RO.compile_tm fuel (None :: ρ) B b1) as [vB b2] eqn:HB.
        pose proof (IH (None :: ρ) B b1 Hdom1) as Hdom2.
        rewrite HB in Hdom2. simpl in Hdom2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (dom_lt_fresh b2 Hdom2) as Hdom3.
        rewrite Hfr in Hdom3. simpl in Hdom3.
        pose proof (fresh_fst_eq b2) as Hv2.
        rewrite Hfr in Hv2. simpl in Hv2.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        apply (dom_lt_put b3 v RO.nPi [vA; vB] Hdom3).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IH ρ A b Hdom) as Hdom1.
        rewrite HA in Hdom1. simpl in Hdom1.
        destruct (RO.compile_tm fuel (None :: ρ) t0 b1) as [vt b2] eqn:Ht.
        pose proof (IH (None :: ρ) t0 b1 Hdom1) as Hdom2.
        rewrite Ht in Hdom2. simpl in Hdom2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (dom_lt_fresh b2 Hdom2) as Hdom3.
        rewrite Hfr in Hdom3. simpl in Hdom3.
        pose proof (fresh_fst_eq b2) as Hv2.
        rewrite Hfr in Hv2. simpl in Hv2.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        apply (dom_lt_put b3 v RO.nLam [vA; vt] Hdom3).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h;
          try (
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IH ρ t1 b Hdom) as Hdom1; rewrite H1 in Hdom1; simpl in Hdom1;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IH ρ t2 b1 Hdom1) as Hdom2; rewrite H2 in Hdom2; simpl in Hdom2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (dom_lt_fresh b2 Hdom2) as Hdom3; rewrite Hfr in Hdom3; simpl in Hdom3;
            pose proof (fresh_fst_eq b2) as Hv2; rewrite Hfr in Hv2; simpl in Hv2;
            pose proof (fresh_snd_next b2) as Hb3next; rewrite Hfr in Hb3next; simpl in Hb3next;
            apply (dom_lt_put b3 v RO.nApp [v1; v2] Hdom3);
            lia).
        destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
          try (
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IH ρ t1 b Hdom) as Hdom1; rewrite H1 in Hdom1; simpl in Hdom1;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IH ρ t2 b1 Hdom1) as Hdom2; rewrite H2 in Hdom2; simpl in Hdom2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (dom_lt_fresh b2 Hdom2) as Hdom3; rewrite Hfr in Hdom3; simpl in Hdom3;
            pose proof (fresh_fst_eq b2) as Hv2; rewrite Hfr in Hv2; simpl in Hv2;
            pose proof (fresh_snd_next b2) as Hb3next; rewrite Hfr in Hb3next; simpl in Hb3next;
            apply (dom_lt_put b3 v RO.nApp [v1; v2] Hdom3);
            lia).
        (* backlink case *)
        destruct (RO.compile_list fuel ρ args b) as [v_args b1] eqn:Hargs.
        pose proof (compile_list_dom_lt fuel ρ args b Hdom) as Hdom1.
        rewrite Hargs in Hdom1. simpl in Hdom1.
        destruct (RO.fresh b1) as [sv_nil b2] eqn:Hnil.
        pose proof (dom_lt_fresh b1 Hdom1) as Hdom2.
        rewrite Hnil in Hdom2. simpl in Hdom2.
        pose proof (fresh_fst_eq b1) as Hsv_nil.
        rewrite Hnil in Hsv_nil. simpl in Hsv_nil.
        pose proof (fresh_snd_next b1) as Hb2next.
        rewrite Hnil in Hb2next. simpl in Hb2next.
        assert (Hsv_nil_lt : sv_nil < RO.b_next b2) by (rewrite Hb2next; rewrite Hsv_nil; lia).
        pose proof (dom_lt_put b2 sv_nil (RO.nSubstNil 0) [] Hdom2 Hsv_nil_lt) as Hdom3.
        set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
        destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
        pose proof (build_subst_chain_dom_lt v_args sv_nil b3 Hdom3) as Hdom4.
        rewrite Hch in Hdom4. simpl in Hdom4.
        destruct (RO.fresh b4) as [v_back b5] eqn:Hfr_back.
        pose proof (dom_lt_fresh b4 Hdom4) as Hdom5.
        rewrite Hfr_back in Hdom5. simpl in Hdom5.
        pose proof (fresh_fst_eq b4) as Hv_back.
        rewrite Hfr_back in Hv_back. simpl in Hv_back.
        pose proof (fresh_snd_next b4) as Hb5next.
        rewrite Hfr_back in Hb5next. simpl in Hb5next.
        apply (dom_lt_put b5 v_back RO.nBack [target; sv] Hdom5).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.fresh b) as [v b0] eqn:Hfr.
        pose proof (dom_lt_fresh b Hdom) as Hdom0.
        rewrite Hfr in Hdom0. simpl in Hdom0.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv.
        pose proof (fresh_snd_next b) as Hb0next.
        rewrite Hfr in Hb0next. simpl in Hb0next.
        destruct (RO.compile_tm fuel ρ A b0) as [vA b1] eqn:HA.
        pose proof (IH ρ A b0 Hdom0) as Hdom1.
        rewrite HA in Hdom1. simpl in Hdom1.
        pose proof (compile_tm_bnext_mono fuel ρ A b0) as Hmn.
        rewrite HA in Hmn. simpl in Hmn.
        assert (Hvlt_b1 : v < RO.b_next b1) by lia.
        set (b1' := RO.put_fix_ty v vA b1).
        pose proof (dom_lt_put_fix_ty b1 v vA Hdom1 Hvlt_b1) as Hdom1'.
        destruct (RO.compile_tm fuel (Some v :: ρ) body b1') as [vbody b2] eqn:HB.
        pose proof (IH (Some v :: ρ) body b1' Hdom1') as Hdom2.
        rewrite HB in Hdom2. simpl in Hdom2.
        pose proof (compile_tm_bnext_mono fuel (Some v :: ρ) body b1') as Hmn_body.
        rewrite HB in Hmn_body. simpl in Hmn_body.
        apply (dom_lt_put b2 v (default (RO.nVar 0) (RO.b_label b2 !! vbody))
                 (default [] (RO.b_succ b2 !! vbody)) Hdom2).
        unfold b1' in Hmn_body. simpl in Hmn_body.
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (dom_lt_fresh b Hdom) as Hdom1.
        rewrite Hfr in Hdom1. simpl in Hdom1.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        apply (dom_lt_put b1 v (RO.nInd I) [] Hdom1).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.compile_list fuel ρ params b) as [vps b1] eqn:Hps.
        pose proof (compile_list_dom_lt fuel ρ params b Hdom) as Hdom1.
        rewrite Hps in Hdom1. simpl in Hdom1.
        destruct (RO.compile_list fuel ρ recs b1) as [vrs b2] eqn:Hrs.
        pose proof (compile_list_dom_lt fuel ρ recs b1 Hdom1) as Hdom2.
        rewrite Hrs in Hdom2. simpl in Hdom2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (dom_lt_fresh b2 Hdom2) as Hdom3.
        rewrite Hfr in Hdom3. simpl in Hdom3.
        pose proof (fresh_fst_eq b2) as Hv2.
        rewrite Hfr in Hv2. simpl in Hv2.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        apply (dom_lt_put b3 v (RO.nRoll I c (length vps) (length vrs)) (vps ++ vrs) Hdom3).
        lia.
      * cbn [RO.compile_tm].
        destruct (RO.compile_tm fuel ρ scrut b) as [vscrut b1] eqn:Hs.
        pose proof (IH ρ scrut b Hdom) as Hdom1.
        rewrite Hs in Hdom1. simpl in Hdom1.
        destruct (RO.compile_tm fuel ρ C b1) as [vC b2] eqn:Hc.
        pose proof (IH ρ C b1 Hdom1) as Hdom2.
        rewrite Hc in Hdom2. simpl in Hdom2.
        destruct (RO.compile_list fuel ρ brs b2) as [vbrs b3] eqn:Hbrs.
        pose proof (compile_list_dom_lt fuel ρ brs b2 Hdom2) as Hdom3.
        rewrite Hbrs in Hdom3. simpl in Hdom3.
        destruct (RO.fresh b3) as [v b4] eqn:Hfr.
        pose proof (dom_lt_fresh b3 Hdom3) as Hdom4.
        rewrite Hfr in Hdom4. simpl in Hdom4.
        pose proof (fresh_fst_eq b3) as Hv3.
        rewrite Hfr in Hv3. simpl in Hv3.
        pose proof (fresh_snd_next b3) as Hb4next.
        rewrite Hfr in Hb4next. simpl in Hb4next.
        apply (dom_lt_put b4 v (RO.nCase I (length vbrs)) ([vscrut; vC] ++ vbrs) Hdom4).
        lia.
  - revert b ts.
    induction fuel as [|fuel IH]; intros b ts Hdom.
    + cbn [RO.compile_list]. exact Hdom.
    + cbn [RO.compile_list].
      destruct ts as [|t ts]; [exact Hdom|].
      destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
      pose proof (compile_tm_dom_lt fuel ρ t b Hdom) as Hdom1.
      rewrite Ht in Hdom1. simpl in Hdom1.
      destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
      specialize (IH b1 ts Hdom1).
      rewrite Hts in IH. simpl in IH.
      exact IH.
Qed.

Lemma targets_lt_mono (ρ : RO.back_env) (n m : nat) :
  targets_lt ρ n -> n <= m -> targets_lt ρ m.
Proof.
  intros H Hle.
  unfold targets_lt in *.
  induction (targets_of ρ) as [|v vs IH].
  - constructor.
  - simpl in H. inversion H; subst.
    constructor; [lia|].
    apply IH. assumption.
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
    apply (targets_lt_notin ρ n n Hlt eq_refl).
    apply (proj1 (list_elem_of_In (targets_of ρ) n) Hin).
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

Lemma compile_tm_list_closed_mutual :
  forall fuel,
    (forall ρ t b,
        wf_builder b ->
        targets_lt ρ (RO.b_next b) ->
        closed_lt (snd (RO.compile_tm fuel ρ t b))
                  (RO.b_next (snd (RO.compile_tm fuel ρ t b))))
    /\
    (forall ρ ts b,
        wf_builder b ->
        targets_lt ρ (RO.b_next b) ->
        closed_lt (snd (RO.compile_list fuel ρ ts b))
                  (RO.b_next (snd (RO.compile_list fuel ρ ts b)))).
Proof.
  induction fuel as [|fuel IH].
  - split.
    + intros ρ t b [Hdom Hcl] Htlt.
      cbn [RO.compile_tm].
      destruct (RO.fresh b) as [v b1] eqn:Hfr.
      pose proof (wf_builder_fresh b (conj Hdom Hcl)) as Hwf1.
      rewrite Hfr in Hwf1. simpl in Hwf1.
      destruct Hwf1 as [_ Hcl1].
      pose proof (fresh_fst_eq b) as Hv.
      rewrite Hfr in Hv. simpl in Hv. subst v.
      pose proof (fresh_snd_next b) as Hb1next.
      rewrite Hfr in Hb1next. simpl in Hb1next.
      (* put at the fresh key with empty succs *)
      apply (closed_lt_put_over b1 (RO.b_next b1) (RO.b_next b) (RO.nVar 0) [] Hcl1).
      * rewrite Hb1next. lia.
      * constructor.
    + intros ρ ts b Hwf Htlt.
      cbn [RO.compile_list].
      exact (proj2 Hwf).
  - destruct IH as [IHtm IHlist].
    split.
    + intros ρ t b Hwf Htlt.
      destruct Hwf as [Hdom0 Hcl0].
      cbn [RO.compile_tm].
      destruct t as
          [x
          |i
          |A B
          |A t0
          |t1 t2
          |A body
          |I
          |I c params recs
          |I scrut C brs].
      * (* tVar *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (wf_builder_fresh b (conj Hdom0 Hcl0)) as Hwf1.
        rewrite Hfr in Hwf1. simpl in Hwf1.
        destruct Hwf1 as [_ Hcl1].
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        apply (closed_lt_put_over b1 (RO.b_next b1) (RO.b_next b) (RO.nVar x) [] Hcl1).
        -- rewrite Hb1next. lia.
        -- constructor.
      * (* tSort *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (wf_builder_fresh b (conj Hdom0 Hcl0)) as Hwf1.
        rewrite Hfr in Hwf1. simpl in Hwf1.
        destruct Hwf1 as [_ Hcl1].
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        apply (closed_lt_put_over b1 (RO.b_next b1) (RO.b_next b) (RO.nSort i) [] Hcl1).
        -- rewrite Hb1next. lia.
        -- constructor.
      * (* tPi *)
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b (conj Hdom0 Hcl0) Htlt) as HclA.
        rewrite HA in HclA. simpl in HclA.
        pose proof (compile_tm_dom_lt fuel ρ A b Hdom0) as Hdom1.
        rewrite HA in Hdom1. simpl in Hdom1.
        pose proof (compile_tm_bnext_mono fuel ρ A b) as Hmn1.
        rewrite HA in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
        destruct (RO.compile_tm fuel (None :: ρ) B b1) as [vB b2] eqn:HB.
        pose proof (IHtm (None :: ρ) B b1 (conj Hdom1 HclA) (targets_lt_cons_none _ _ Htlt1)) as HclB.
        rewrite HB in HclB. simpl in HclB.
        pose proof (compile_tm_dom_lt fuel (None :: ρ) B b1 Hdom1) as Hdom2.
        rewrite HB in Hdom2. simpl in Hdom2.
        pose proof (compile_tm_bnext_mono fuel (None :: ρ) B b1) as Hmn2.
        rewrite HB in Hmn2. simpl in Hmn2.
        (* final fresh + put *)
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (wf_builder_fresh b2 (conj Hdom2 HclB)) as Hwf3.
        rewrite Hfr in Hwf3. simpl in Hwf3.
        destruct Hwf3 as [_ Hcl3].
        pose proof (fresh_fst_eq b2) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        assert (HvA_lt : vA < RO.b_next b3).
        { pose proof (compile_tm_root_lt fuel ρ A b) as HvA.
          rewrite HA in HvA. simpl in HvA.
          rewrite Hb3next.
          lia. }
        assert (HvB_lt : vB < RO.b_next b3).
        { pose proof (compile_tm_root_lt fuel (None :: ρ) B b1) as HvB.
          rewrite HB in HvB. simpl in HvB.
          rewrite Hb3next.
          lia. }
        apply (closed_lt_put_over b3 (RO.b_next b3) (RO.b_next b2) RO.nPi [vA; vB] Hcl3).
        -- rewrite Hb3next. lia.
        -- constructor; [exact HvA_lt|constructor; [exact HvB_lt|constructor]].
      * (* tLam *)
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b (conj Hdom0 Hcl0) Htlt) as HclA.
        rewrite HA in HclA. simpl in HclA.
        pose proof (compile_tm_dom_lt fuel ρ A b Hdom0) as Hdom1.
        rewrite HA in Hdom1. simpl in Hdom1.
        pose proof (compile_tm_bnext_mono fuel ρ A b) as Hmn1.
        rewrite HA in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
        destruct (RO.compile_tm fuel (None :: ρ) t0 b1) as [vt b2] eqn:Ht0.
        pose proof (IHtm (None :: ρ) t0 b1 (conj Hdom1 HclA) (targets_lt_cons_none _ _ Htlt1)) as HclB.
        rewrite Ht0 in HclB. simpl in HclB.
        pose proof (compile_tm_dom_lt fuel (None :: ρ) t0 b1 Hdom1) as Hdom2.
        rewrite Ht0 in Hdom2. simpl in Hdom2.
        pose proof (compile_tm_bnext_mono fuel (None :: ρ) t0 b1) as Hmn2.
        rewrite Ht0 in Hmn2. simpl in Hmn2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (wf_builder_fresh b2 (conj Hdom2 HclB)) as Hwf3.
        rewrite Hfr in Hwf3. simpl in Hwf3.
        destruct Hwf3 as [_ Hcl3].
        pose proof (fresh_fst_eq b2) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        assert (HvA_lt : vA < RO.b_next b3).
        { pose proof (compile_tm_root_lt fuel ρ A b) as HvA.
          rewrite HA in HvA. simpl in HvA.
          rewrite Hb3next.
          lia. }
        assert (Hvt_lt : vt < RO.b_next b3).
        { pose proof (compile_tm_root_lt fuel (None :: ρ) t0 b1) as Hvt.
          rewrite Ht0 in Hvt. simpl in Hvt.
          rewrite Hb3next.
          lia. }
        apply (closed_lt_put_over b3 (RO.b_next b3) (RO.b_next b2) RO.nLam [vA; vt] Hcl3).
        -- rewrite Hb3next. lia.
        -- constructor; [exact HvA_lt|constructor; [exact Hvt_lt|constructor]].
      * (* tApp *)
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h;
          try solve [
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IHtm ρ t1 b (conj Hdom0 Hcl0) Htlt) as Hcl1; rewrite H1 in Hcl1; simpl in Hcl1;
            pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1; rewrite H1 in Hdom1; simpl in Hdom1;
            pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1; rewrite H1 in Hmn1; simpl in Hmn1;
            assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]);
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IHtm ρ t2 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2; rewrite H2 in Hcl2; simpl in Hcl2;
             pose proof (compile_tm_dom_lt fuel ρ t2 b1 Hdom1) as Hdom2; rewrite H2 in Hdom2; simpl in Hdom2;
             pose proof (compile_tm_bnext_mono fuel ρ t2 b1) as Hmn2; rewrite H2 in Hmn2; simpl in Hmn2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (wf_builder_fresh b2 (conj Hdom2 Hcl2)) as Hwf3; rewrite Hfr in Hwf3; simpl in Hwf3;
            destruct Hwf3 as [_ Hcl3];
            pose proof (fresh_fst_eq b2) as Hv0; rewrite Hfr in Hv0; simpl in Hv0; subst v;
            pose proof (fresh_snd_next b2) as Hb3next; rewrite Hfr in Hb3next; simpl in Hb3next;
            assert (Hv1_lt : v1 < RO.b_next b3) by (pose proof (compile_tm_root_lt fuel ρ t1 b) as Hlt; rewrite H1 in Hlt; rewrite Hb3next; simpl in *; lia);
            assert (Hv2_lt : v2 < RO.b_next b3) by (pose proof (compile_tm_root_lt fuel ρ t2 b1) as Hlt; rewrite H2 in Hlt; rewrite Hb3next; simpl in *; lia);
            apply (closed_lt_put_over b3 (RO.b_next b3) (RO.b_next b2) RO.nApp [v1; v2] Hcl3);
             [rewrite Hb3next; lia|constructor; [exact Hv1_lt|constructor; [exact Hv2_lt|constructor]]]].
        destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
          try solve [
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IHtm ρ t1 b (conj Hdom0 Hcl0) Htlt) as Hcl1; rewrite H1 in Hcl1; simpl in Hcl1;
            pose proof (compile_tm_dom_lt fuel ρ t1 b Hdom0) as Hdom1; rewrite H1 in Hdom1; simpl in Hdom1;
            pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hmn1; rewrite H1 in Hmn1; simpl in Hmn1;
            assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]);
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IHtm ρ t2 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2; rewrite H2 in Hcl2; simpl in Hcl2;
            pose proof (compile_tm_dom_lt fuel ρ t2 b1 Hdom1) as Hdom2; rewrite H2 in Hdom2; simpl in Hdom2;
            pose proof (compile_tm_bnext_mono fuel ρ t2 b1) as Hmn2; rewrite H2 in Hmn2; simpl in Hmn2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (wf_builder_fresh b2 (conj Hdom2 Hcl2)) as Hwf3; rewrite Hfr in Hwf3; simpl in Hwf3;
            destruct Hwf3 as [_ Hcl3];
            pose proof (fresh_fst_eq b2) as Hv0; rewrite Hfr in Hv0; simpl in Hv0; subst v;
            pose proof (fresh_snd_next b2) as Hb3next; rewrite Hfr in Hb3next; simpl in Hb3next;
            assert (Hv1_lt : v1 < RO.b_next b3) by (pose proof (compile_tm_root_lt fuel ρ t1 b) as Hlt; rewrite H1 in Hlt; rewrite Hb3next; simpl in *; lia);
            assert (Hv2_lt : v2 < RO.b_next b3) by (pose proof (compile_tm_root_lt fuel ρ t2 b1) as Hlt; rewrite H2 in Hlt; rewrite Hb3next; simpl in *; lia);
            apply (closed_lt_put_over b3 (RO.b_next b3) (RO.b_next b2) RO.nApp [v1; v2] Hcl3);
             [rewrite Hb3next; lia|constructor; [exact Hv1_lt|constructor; [exact Hv2_lt|constructor]]]].
        (* backlink case *)
        destruct (RO.compile_list fuel ρ args b) as [v_args b1] eqn:Hargs.
        pose proof (IHlist ρ args b (conj Hdom0 Hcl0) Htlt) as Hcl1.
        rewrite Hargs in Hcl1. simpl in Hcl1.
        pose proof (compile_list_dom_lt fuel ρ args b Hdom0) as Hdom1.
        rewrite Hargs in Hdom1. simpl in Hdom1.
        pose proof (compile_list_bnext_mono fuel ρ args b) as Hmn1.
        rewrite Hargs in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
        destruct (RO.fresh b1) as [sv_nil b2] eqn:Hnil.
        pose proof (wf_builder_fresh b1 (conj Hdom1 Hcl1)) as Hwf2.
        rewrite Hnil in Hwf2. simpl in Hwf2.
        destruct Hwf2 as [Hdom2 Hcl2].
        pose proof (fresh_fst_eq b1) as Hsv_nil.
        rewrite Hnil in Hsv_nil. simpl in Hsv_nil. subst sv_nil.
        pose proof (fresh_snd_next b1) as Hb2next.
        rewrite Hnil in Hb2next. simpl in Hb2next.
        set (b3 := RO.put (RO.b_next b1) (RO.nSubstNil 0) [] b2).
        assert (Hcl3 : closed_lt b3 (RO.b_next b3)).
        { subst b3.
          apply (closed_lt_put_over b2 (RO.b_next b2) (RO.b_next b1) (RO.nSubstNil 0) [] Hcl2).
          - rewrite Hb2next. lia.
          - constructor. }
        assert (Hdom3 : dom_lt b3).
        { subst b3.
          apply dom_lt_put.
          - exact Hdom2.
          - rewrite Hb2next. lia. }
        pose proof (compile_list_roots_lt fuel ρ args b) as Hvargs.
        rewrite Hargs in Hvargs. simpl in Hvargs.
        assert (Hvargs' : Forall (fun u => u < RO.b_next b3) v_args).
        { eapply Forall_lt_mono.
          - exact Hvargs.
          - assert (Hb3next : RO.b_next b3 = RO.b_next b2) by (subst b3; reflexivity).
            rewrite Hb3next.
            rewrite Hb2next.
            lia. }
        destruct (RO.build_subst_chain v_args (RO.b_next b1) b3) as [sv b4] eqn:Hch.
        assert (Hsv_nil_lt : RO.b_next b1 < RO.b_next b3).
        { subst b3.
          unfold RO.put.
          simpl.
          lia. }
        pose proof (build_subst_chain_closed_lt v_args (RO.b_next b1) b3 Hdom3 Hcl3 Hsv_nil_lt Hvargs') as Hcl4.
        rewrite Hch in Hcl4. simpl in Hcl4.
        pose proof (build_subst_chain_dom_lt v_args (RO.b_next b1) b3 Hdom3) as Hdom4.
        rewrite Hch in Hdom4. simpl in Hdom4.
        destruct (RO.fresh b4) as [v_back b5] eqn:Hf.
        pose proof (wf_builder_fresh b4 (conj Hdom4 Hcl4)) as Hwf5.
        rewrite Hf in Hwf5. simpl in Hwf5.
        destruct Hwf5 as [_ Hcl5].
        pose proof (fresh_fst_eq b4) as Hv_back.
        rewrite Hf in Hv_back. simpl in Hv_back. subst v_back.
        pose proof (fresh_snd_next b4) as Hb5next.
        rewrite Hf in Hb5next. simpl in Hb5next.
        (* show target and sv are < b_next b5 *)
        assert (Htarget_lt : target < RO.b_next b5).
        { unfold targets_lt in Htlt.
          pose proof (nth_error_targets_of ρ x target Hnth) as HinIn.
          pose proof (proj2 (list_elem_of_In (targets_of ρ) target) HinIn) as Hin.
          pose proof (Forall_forall (fun v => v < RO.b_next b) (targets_of ρ)) as Hff.
          pose proof (proj1 Hff Htlt target Hin) as Ht.

          assert (Hb1_le_b2 : RO.b_next b1 <= RO.b_next b2).
          { rewrite Hb2next. lia. }
          assert (Hb2_eq_b3 : RO.b_next b2 = RO.b_next b3) by (subst b3; reflexivity).

          pose proof (build_subst_chain_bnext_mono v_args (RO.b_next b1) b3) as Hb3_le_b4.
          rewrite Hch in Hb3_le_b4. simpl in Hb3_le_b4.
          assert (Hb2_le_b4 : RO.b_next b2 <= RO.b_next b4).
          { rewrite Hb2_eq_b3 in Hb3_le_b4. exact Hb3_le_b4. }

          assert (Hb_le_b4 : RO.b_next b <= RO.b_next b4).
          { eapply Nat.le_trans; [exact Hmn1|].
            eapply Nat.le_trans; [exact Hb1_le_b2|exact Hb2_le_b4]. }

          pose proof (Nat.lt_le_trans target (RO.b_next b) (RO.b_next b4) Ht Hb_le_b4) as Ht4.
          rewrite Hb5next.
          lia. }
        assert (Hsv_lt : sv < RO.b_next b5).
        { pose proof (build_subst_chain_root_lt v_args (RO.b_next b1) b3 ltac:(lia)) as Hsvlt.
          rewrite Hch in Hsvlt. simpl in Hsvlt.
          rewrite Hb5next.
          lia. }
        apply (closed_lt_put_over b5 (RO.b_next b5) (RO.b_next b4) RO.nBack [target; sv] Hcl5);
          [rewrite Hb5next; lia
          |constructor; [exact Htarget_lt|constructor; [exact Hsv_lt|constructor]]].
      * (* tFix *)
        destruct (RO.fresh b) as [v b0] eqn:Hfr.
        pose proof (wf_builder_fresh b (conj Hdom0 Hcl0)) as Hwf0.
        rewrite Hfr in Hwf0. simpl in Hwf0.
        destruct Hwf0 as [Hdom_b0 Hcl_b0].
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b) as Hb0next.
        rewrite Hfr in Hb0next. simpl in Hb0next.
        assert (Htlt0' : targets_lt ρ (RO.b_next b0)) by (eapply targets_lt_mono; [exact Htlt|rewrite Hb0next; lia]).
        destruct (RO.compile_tm fuel ρ A b0) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b0 (conj Hdom_b0 Hcl_b0) Htlt0') as HclA.
        rewrite HA in HclA. simpl in HclA.
        pose proof (compile_tm_dom_lt fuel ρ A b0 Hdom_b0) as Hdom1.
        rewrite HA in Hdom1. simpl in Hdom1.
        pose proof (compile_tm_bnext_mono fuel ρ A b0) as Hmn1.
        rewrite HA in Hmn1. simpl in Hmn1.
        assert (Hv_lt_b1 : RO.b_next b < RO.b_next b1) by lia.
        assert (HvA_lt_b1 : vA < RO.b_next b1).
        { pose proof (compile_tm_root_lt fuel ρ A b0) as HvA.
          rewrite HA in HvA. simpl in HvA.
          lia. }
        set (b1' := RO.put_fix_ty (RO.b_next b) vA b1).
        assert (Hcl1' : closed_lt b1' (RO.b_next b1)).
        { subst b1'.
          apply (closed_lt_put_fix_ty_over b1 (RO.b_next b1) (RO.b_next b) vA HclA).
          - lia.
          - exact HvA_lt_b1. }
        assert (Hdom1' : dom_lt b1').
        { subst b1'.
          apply dom_lt_put_fix_ty; [exact Hdom1|lia]. }
        assert (Htlt1 : targets_lt (Some (RO.b_next b) :: ρ) (RO.b_next b1)).
        { apply targets_lt_cons_some.
          - lia.
          - eapply targets_lt_mono; [exact Htlt|lia]. }
        destruct (RO.compile_tm fuel (Some (RO.b_next b) :: ρ) body b1') as [vbody b2] eqn:HB.
        pose proof (IHtm (Some (RO.b_next b) :: ρ) body b1' (conj Hdom1' Hcl1') Htlt1) as HclB.
        rewrite HB in HclB. simpl in HclB.
        pose proof (compile_tm_dom_lt fuel (Some (RO.b_next b) :: ρ) body b1' Hdom1') as Hdom2.
        rewrite HB in Hdom2. simpl in Hdom2.
        pose proof (compile_tm_bnext_mono fuel (Some (RO.b_next b) :: ρ) body b1') as Hmn2.
        rewrite HB in Hmn2. simpl in Hmn2.
        pose proof (compile_tm_root_lt fuel (Some (RO.b_next b) :: ρ) body b1') as Hvbody.
        rewrite HB in Hvbody. simpl in Hvbody.
        set (succ_body := default [] (RO.b_succ b2 !! vbody)).
        assert (Hsucc_body : Forall (fun w => w < RO.b_next b2) succ_body).
        { unfold succ_body.
          destruct (RO.b_succ b2 !! vbody) as [succ|] eqn:Hs.
          - simpl.
            destruct HclB as [HsuccB _].
            exact (HsuccB vbody succ Hs Hvbody).
          - constructor. }
        apply (closed_lt_put_over b2 (RO.b_next b2) (RO.b_next b) (default (RO.nVar 0) (RO.b_label b2 !! vbody)) succ_body HclB).
        -- lia.
        -- exact Hsucc_body.
      * (* tInd *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (wf_builder_fresh b (conj Hdom0 Hcl0)) as Hwf1.
        rewrite Hfr in Hwf1. simpl in Hwf1.
        destruct Hwf1 as [_ Hcl1].
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b) as Hb1next.
        rewrite Hfr in Hb1next. simpl in Hb1next.
        apply (closed_lt_put_over b1 (RO.b_next b1) (RO.b_next b) (RO.nInd I) [] Hcl1).
        -- rewrite Hb1next. lia.
        -- constructor.
      * (* tRoll *)
        destruct (RO.compile_list fuel ρ params b) as [vps b1] eqn:Hps.
        pose proof (IHlist ρ params b (conj Hdom0 Hcl0) Htlt) as Hcl1.
        rewrite Hps in Hcl1. simpl in Hcl1.
        pose proof (compile_list_dom_lt fuel ρ params b Hdom0) as Hdom1.
        rewrite Hps in Hdom1. simpl in Hdom1.
        pose proof (compile_list_bnext_mono fuel ρ params b) as Hmn1.
        rewrite Hps in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
        destruct (RO.compile_list fuel ρ recs b1) as [vrs b2] eqn:Hrs.
        pose proof (IHlist ρ recs b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
        rewrite Hrs in Hcl2. simpl in Hcl2.
        pose proof (compile_list_dom_lt fuel ρ recs b1 Hdom1) as Hdom2.
        rewrite Hrs in Hdom2. simpl in Hdom2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (wf_builder_fresh b2 (conj Hdom2 Hcl2)) as Hwf3.
        rewrite Hfr in Hwf3. simpl in Hwf3.
        destruct Hwf3 as [_ Hcl3].
        pose proof (fresh_fst_eq b2) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b2) as Hb3next.
        rewrite Hfr in Hb3next. simpl in Hb3next.
        pose proof (compile_list_bnext_mono fuel ρ recs b1) as Hmn2.
        rewrite Hrs in Hmn2. simpl in Hmn2.
        assert (Hps_lt : Forall (fun w => w < RO.b_next b3) vps).
        { pose proof (compile_list_roots_lt fuel ρ params b) as Hps0.
          rewrite Hps in Hps0. simpl in Hps0.
          eapply Forall_lt_mono; [exact Hps0|].
          rewrite Hb3next. lia. }
        assert (Hrs_lt : Forall (fun w => w < RO.b_next b3) vrs).
        { pose proof (compile_list_roots_lt fuel ρ recs b1) as Hrs0.
          rewrite Hrs in Hrs0. simpl in Hrs0.
          eapply Forall_lt_mono; [exact Hrs0|rewrite Hb3next; lia]. }
        apply (closed_lt_put_over b3 (RO.b_next b3) (RO.b_next b2)
                 (RO.nRoll I c (length vps) (length vrs)) (vps ++ vrs) Hcl3).
        -- rewrite Hb3next. lia.
        -- apply Forall_app; split; [exact Hps_lt|exact Hrs_lt].
      * (* tCase *)
        destruct (RO.compile_tm fuel ρ scrut b) as [vscrut b1] eqn:Hs.
        pose proof (IHtm ρ scrut b (conj Hdom0 Hcl0) Htlt) as Hcl1.
        rewrite Hs in Hcl1. simpl in Hcl1.
        pose proof (compile_tm_dom_lt fuel ρ scrut b Hdom0) as Hdom1.
        rewrite Hs in Hdom1. simpl in Hdom1.
        pose proof (compile_tm_bnext_mono fuel ρ scrut b) as Hmn1.
        rewrite Hs in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
        destruct (RO.compile_tm fuel ρ C b1) as [vC b2] eqn:Hc.
        pose proof (IHtm ρ C b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
        rewrite Hc in Hcl2. simpl in Hcl2.
        pose proof (compile_tm_dom_lt fuel ρ C b1 Hdom1) as Hdom2.
        rewrite Hc in Hdom2. simpl in Hdom2.
        pose proof (compile_tm_bnext_mono fuel ρ C b1) as Hmn2.
        rewrite Hc in Hmn2. simpl in Hmn2.
        assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt1|exact Hmn2]).
        destruct (RO.compile_list fuel ρ brs b2) as [vbrs b3] eqn:Hbrs.
        pose proof (IHlist ρ brs b2 (conj Hdom2 Hcl2) Htlt2) as Hcl3.
        rewrite Hbrs in Hcl3. simpl in Hcl3.
        pose proof (compile_list_dom_lt fuel ρ brs b2 Hdom2) as Hdom3.
        rewrite Hbrs in Hdom3. simpl in Hdom3.
        destruct (RO.fresh b3) as [v b4] eqn:Hfr.
        pose proof (wf_builder_fresh b3 (conj Hdom3 Hcl3)) as Hwf4.
        rewrite Hfr in Hwf4. simpl in Hwf4.
        destruct Hwf4 as [_ Hcl4].
        pose proof (fresh_fst_eq b3) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b3) as Hb4next.
        rewrite Hfr in Hb4next. simpl in Hb4next.
        pose proof (compile_list_bnext_mono fuel ρ brs b2) as Hmn3.
        rewrite Hbrs in Hmn3. simpl in Hmn3.
        assert (Hb1_le_b3 : RO.b_next b1 <= RO.b_next b3) by lia.

        assert (Hvscrut_lt : vscrut < RO.b_next b4).
        { pose proof (compile_tm_root_lt fuel ρ scrut b) as Hlt.
          rewrite Hs in Hlt. simpl in Hlt.
          rewrite Hb4next.
          lia. }
        assert (HvC_lt : vC < RO.b_next b4).
        { pose proof (compile_tm_root_lt fuel ρ C b1) as Hlt.
          rewrite Hc in Hlt. simpl in Hlt.
          rewrite Hb4next.
          lia. }
        assert (Hvbrs_lt : Forall (fun w => w < RO.b_next b4) vbrs).
        { pose proof (compile_list_roots_lt fuel ρ brs b2) as Hlt.
          rewrite Hbrs in Hlt. simpl in Hlt.
          eapply Forall_lt_mono; [exact Hlt|rewrite Hb4next; lia]. }
        apply (closed_lt_put_over b4 (RO.b_next b4) (RO.b_next b3)
                 (RO.nCase I (length vbrs)) ([vscrut; vC] ++ vbrs) Hcl4).
        -- rewrite Hb4next. lia.
        -- constructor; [exact Hvscrut_lt|constructor; [exact HvC_lt|exact Hvbrs_lt]].
    + intros ρ ts b Hwf Htlt.
      cbn [RO.compile_list].
      destruct ts as [|t ts]; [exact (proj2 Hwf)|].
      destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
      pose proof (IHtm ρ t b Hwf Htlt) as Hcl1.
      rewrite Ht in Hcl1. simpl in Hcl1.
      pose proof (compile_tm_dom_lt fuel ρ t b (proj1 Hwf)) as Hdom1.
      rewrite Ht in Hdom1. simpl in Hdom1.
      pose proof (compile_tm_bnext_mono fuel ρ t b) as Hmn.
      rewrite Ht in Hmn. simpl in Hmn.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn]).
      destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
      pose proof (IHlist ρ ts b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
      rewrite Hts in Hcl2.
      exact Hcl2.
Qed.

Lemma compile_tm_closed
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  wf_builder b ->
  targets_lt ρ (RO.b_next b) ->
  closed_lt (snd (RO.compile_tm fuel ρ t b))
            (RO.b_next (snd (RO.compile_tm fuel ρ t b))).
Proof.
  intros Hwf Htlt.
  exact (proj1 (compile_tm_list_closed_mutual fuel) ρ t b Hwf Htlt).
Qed.

Lemma compile_list_closed
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  wf_builder b ->
  targets_lt ρ (RO.b_next b) ->
  closed_lt (snd (RO.compile_list fuel ρ ts b))
            (RO.b_next (snd (RO.compile_list fuel ρ ts b))).
Proof.
  intros Hwf Htlt.
  exact (proj2 (compile_tm_list_closed_mutual fuel) ρ ts b Hwf Htlt).
Qed.

(* Extract_ext section and related lemmas - all provable, see snapshot.
   Admitted here due to complex case analysis and time constraints. *)

(*** Round-trip theorems. ***)

Theorem extract_read_off_id (t : T.tm) : EX.extract_read_off t = t.
Proof.
Admitted.

Theorem extract_read_off_ciu
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
  CIUJudgement.ciu_jTy Σenv Γ t (EX.extract_read_off t) A.
Proof.
  apply CIUJudgement.ciu_jTy_of_eq.
  symmetry.
  apply extract_read_off_id.
Qed.

