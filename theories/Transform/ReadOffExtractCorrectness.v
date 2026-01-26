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

(** Compilation fuel wrappers.

    `ReadOff.compile_list` consumes fuel per list cell, so we use the
    compilation fuel measure `RO.fuel_tm` / `RO.fuel_list RO.fuel_tm`.
*)
Definition compile_fuel_tm (t : T.tm) : nat := RO.fuel_tm t.
Definition compile_fuel_list (ts : list T.tm) : nat := RO.fuel_list RO.fuel_tm ts.

Lemma compile_fuel_tm_ge_1 (t : T.tm) : 1 <= compile_fuel_tm t.
Proof.
  induction t; cbn [compile_fuel_tm RO.fuel_tm compile_fuel_list RO.fuel_list]; lia.
Qed.

Lemma compile_fuel_list_nil : compile_fuel_list [] = 0.
Proof. reflexivity. Qed.

Lemma compile_fuel_list_cons (t : T.tm) (ts : list T.tm) :
  compile_fuel_list (t :: ts) = S (compile_fuel_tm t + compile_fuel_list ts).
Proof. reflexivity. Qed.

Lemma compile_fuel_tm_ge_size (t : T.tm) : S (T.size t) <= compile_fuel_tm t.
Proof.
  induction t; cbn [compile_fuel_tm RO.fuel_tm T.size compile_fuel_list RO.fuel_list]; try lia.
  - (* tRoll *)
    (* reduce to list bounds *)
    assert (Hparams : fold_right (fun u n => T.size u + n) 0 params <= compile_fuel_list params).
    { induction params as [|p ps IHps]; cbn [compile_fuel_list RO.fuel_list fold_right]; [lia|].
      specialize (IHt p).
      specialize (IHps).
      lia. }
    assert (Hrecs : fold_right (fun u n => T.size u + n) 0 recs <= compile_fuel_list recs).
    { induction recs as [|r rs IHrs]; cbn [compile_fuel_list RO.fuel_list fold_right]; [lia|].
      specialize (IHt r).
      specialize (IHrs).
      lia. }
    cbn [compile_fuel_tm RO.fuel_tm].
    cbn [T.size].
    lia.
  - (* tCase *)
    assert (Hbrs : fold_right (fun u n => T.size u + n) 0 brs <= compile_fuel_list brs).
    { induction brs as [|br brs IHbrs]; cbn [compile_fuel_list RO.fuel_list fold_right]; [lia|].
      specialize (IHt br).
      specialize (IHbrs).
      lia. }
    cbn [compile_fuel_tm RO.fuel_tm].
    cbn [T.size].
    lia.
Qed.

Lemma compile_fuel_list_ge_list_size (ts : list T.tm) : list_size ts <= compile_fuel_list ts.
Proof.
  destruct ts as [|t ts]; cbn [list_size compile_fuel_list RO.fuel_list]; [lia|].
  (* list_size = length + S(max size); our fuel_list is a sum, hence >= max and >= length *)
  assert (Hlen : length (t :: ts) <= S (compile_fuel_tm t + compile_fuel_list ts)).
  { (* fuel adds 1 per cell *)
    induction ts as [|u us IH]; cbn [compile_fuel_list RO.fuel_list length]; lia. }
  assert (Hmax : S (list_max_size (t :: ts)) <= S (compile_fuel_tm t + compile_fuel_list ts)).
  { (* max size bounded by sum of sizes, then by fuel *)
    pose proof (compile_fuel_tm_ge_size t) as Ht.
    assert (Hsum : list_max_size (t :: ts) <= fold_right (fun u n => T.size u + n) 0 (t :: ts)).
    { apply list_max_size_le_sum_sizes. }
    assert (Hfuel_sum : fold_right (fun u n => T.size u + n) 0 (t :: ts) <= compile_fuel_list (t :: ts)).
    { cbn [compile_fuel_list RO.fuel_list].
      (* crude: each element contributes at least its size *)
      induction ts as [|u us IH]; cbn [compile_fuel_list RO.fuel_list fold_right]; try lia.
      pose proof (compile_fuel_tm_ge_size u) as Hu.
      lia. }
    cbn [compile_fuel_list RO.fuel_list] in Hfuel_sum.
    lia. }
  lia.
Qed.

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

Lemma fix_env_of_lookup_None_of_targets_lt (ρ : RO.back_env) (n : nat) :
  targets_lt ρ n -> fix_env_of ρ !! n = None.
Proof.
  revert n.
  induction ρ as [|o ρ IH]; intros n Hlt.
  - rewrite fix_env_of_nil. apply lookup_empty.
  - destruct o as [target|].
    + simpl in Hlt.
      inversion Hlt as [|x xs Hx Hxs]; subst.
      rewrite fix_env_of_cons_some.
      destruct (decide (target = n)) as [->|Hne].
      * exfalso. lia.
      * rewrite (lookup_insert_ne (H6:=_) (EX.env_shift (fix_env_of ρ)) target n 0 Hne).
        unfold EX.env_shift.
        pose proof (IH n Hxs) as Hnone.
        rewrite (lookup_fmap (FinMap:=_) S (fix_env_of ρ) n).
        change (S <$> fix_env_of ρ !! n) with (S <$> (fix_env_of ρ !! n)).
        rewrite Hnone.
        simpl. reflexivity.
    + rewrite fix_env_of_cons_none.
      simpl in Hlt.
      unfold EX.env_shift.
      pose proof (IH n Hlt) as Hnone.
      rewrite (lookup_fmap (FinMap:=_) S (fix_env_of ρ) n).
      change (S <$> fix_env_of ρ !! n) with (S <$> (fix_env_of ρ !! n)).
      rewrite Hnone.
      simpl. reflexivity.
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

Lemma extract_vs_eq_extract_list (fuel : nat) (b : RO.builder) (ρ : EX.fix_env) (vs : list nat) :
  extract_vs fuel b ρ vs = EX.extract_list EX.extract_v fuel b ρ vs.
Proof.
  revert vs.
  induction fuel as [|fuel IH]; intros vs; cbn [extract_vs EX.extract_list];
    destruct vs as [|v vs]; cbn [extract_vs EX.extract_list]; auto.
  f_equal.
  apply IH.
Qed.

(* Substitution evidence chains are built by `RO.build_subst_chain` in `ReadOff.v`.
   We prove correctness for extraction (`EX.subst_args`) below. *)

(** Builder domain invariant: no keys >= b_next. *)
Definition dom_lt (b : RO.builder) : Prop :=
  (forall k n, b.(RO.b_label) !! k = Some n -> k < b.(RO.b_next))
  /\ (forall k s, b.(RO.b_succ) !! k = Some s -> k < b.(RO.b_next))
  /\ (forall k vA, b.(RO.b_fix_ty) !! k = Some vA -> k < b.(RO.b_next))
  /\ (forall k vbody, b.(RO.b_fix_body) !! k = Some vbody -> k < b.(RO.b_next)).

Lemma dom_lt_empty : dom_lt RO.empty_builder.
Proof.
  repeat split; intros; simpl in H; rewrite lookup_empty in H; discriminate.
Qed.

Lemma dom_lt_put (b : RO.builder) (v : nat) (lbl : RO.node) (succ : list nat) :
  dom_lt b -> v < RO.b_next b -> dom_lt (RO.put v lbl succ b).
Proof.
  intros [Hl [Hs [Hf Hb]]] Hv.
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
  - intros k vbody Hk.
    simpl in Hk.
    apply Hb in Hk. exact Hk.
Qed.

Lemma dom_lt_put_fix_ty (b : RO.builder) (v vA : nat) :
  dom_lt b -> v < RO.b_next b -> dom_lt (RO.put_fix_ty v vA b).
Proof.
  intros [Hl [Hs [Hf Hb]]] Hv.
  repeat split.
  - intros k n Hk. apply Hl in Hk. exact Hk.
  - intros k s Hk. apply Hs in Hk. exact Hk.
  - intros k w Hk.
    destruct (decide (k = v)) as [->|Hne].
    + simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by (intros Heq; apply Hne; now symmetry).
      apply Hf in Hk. exact Hk.
  - intros k vbody Hk.
    simpl in Hk.
    apply Hb in Hk. exact Hk.
Qed.

Lemma dom_lt_put_fix_body (b : RO.builder) (v vbody : nat) :
  dom_lt b -> v < RO.b_next b -> dom_lt (RO.put_fix_body v vbody b).
Proof.
  intros [Hl [Hs [Hf Hb]]] Hv.
  repeat split.
  - intros k n Hk. apply Hl in Hk. exact Hk.
  - intros k s Hk. apply Hs in Hk. exact Hk.
  - intros k vA Hk. apply Hf in Hk. exact Hk.
  - intros k w Hk.
    destruct (decide (k = v)) as [->|Hne].
    + simpl. exact Hv.
    + simpl in Hk.
      rewrite lookup_insert_ne in Hk by (intros Heq; apply Hne; now symmetry).
      apply Hb in Hk. exact Hk.
Qed.

Lemma dom_lt_fresh (b : RO.builder) :
  dom_lt b ->
  dom_lt (snd (RO.fresh b)).
Proof.
  intros [Hl [Hs [Hf Hb]]].
  unfold RO.fresh.
  simpl.
  repeat split.
  - intros k n Hk. specialize (Hl k n Hk). exact (Nat.lt_lt_succ_r _ _ Hl).
  - intros k s Hk. specialize (Hs k s Hk). exact (Nat.lt_lt_succ_r _ _ Hs).
  - intros k vA Hk. specialize (Hf k vA Hk). exact (Nat.lt_lt_succ_r _ _ Hf).
  - intros k vbody Hk. specialize (Hb k vbody Hk). exact (Nat.lt_lt_succ_r _ _ Hb).
Qed.

(** Compilation never overwrites existing vertices < old `b_next`. *)
Definition preserves_lt (b b' : RO.builder) : Prop :=
  forall k,
    k < RO.b_next b ->
    b'.(RO.b_label) !! k = b.(RO.b_label) !! k
    /\ b'.(RO.b_succ) !! k = b.(RO.b_succ) !! k
    /\ b'.(RO.b_fix_ty) !! k = b.(RO.b_fix_ty) !! k
    /\ b'.(RO.b_fix_body) !! k = b.(RO.b_fix_body) !! k.

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
  /\ (forall k vA, b.(RO.b_fix_ty) !! k = Some vA -> k < n -> vA < n)
  /\ (forall k vbody, b.(RO.b_fix_body) !! k = Some vbody -> k < n -> vbody < n).

Lemma preserves_lt_trans (b0 b1 b2 : RO.builder) :
  preserves_lt b0 b1 -> preserves_lt b1 b2 ->
  RO.b_next b0 <= RO.b_next b1 ->
  preserves_lt b0 b2.
Proof.
  intros H01 H12 Hle k Hk.
  specialize (H01 k Hk) as [Hl01 [Hs01 [Hf01 Hb01]]].
  assert (k < RO.b_next b1) by lia.
  specialize (H12 k H) as [Hl12 [Hs12 [Hf12 Hb12]]].
  repeat split; congruence.
Qed.

Lemma preserves_lt_put_over (b b0 : RO.builder) (v : nat) (lbl : RO.node) (succ : list nat) :
  preserves_lt b b0 ->
  v >= RO.b_next b ->
  preserves_lt b (RO.put v lbl succ b0).
Proof.
  intros Hpres Hv k Hk.
  specialize (Hpres k Hk) as [Hlbl [Hsucc [Hfix Hbody]]].
  assert (Hneq : v <> k) by lia.
  unfold RO.put; simpl.
  repeat split.
  - rewrite lookup_insert_ne by exact Hneq. exact Hlbl.
  - rewrite lookup_insert_ne by exact Hneq. exact Hsucc.
  - exact Hfix.
  - exact Hbody.
Qed.

Lemma preserves_lt_put_fix_ty_over (b b0 : RO.builder) (v vA : nat) :
  preserves_lt b b0 ->
  v >= RO.b_next b ->
  preserves_lt b (RO.put_fix_ty v vA b0).
Proof.
  intros Hpres Hv k Hk.
  specialize (Hpres k Hk) as [Hlbl [Hsucc [Hfix Hbody]]].
  assert (Hneq : v <> k) by lia.
  unfold RO.put_fix_ty; simpl.
  repeat split.
  - exact Hlbl.
  - exact Hsucc.
  - rewrite lookup_insert_ne by exact Hneq. exact Hfix.
  - exact Hbody.
Qed.

Lemma preserves_lt_put_fix_body_over (b b0 : RO.builder) (v vbody : nat) :
  preserves_lt b b0 ->
  v >= RO.b_next b ->
  preserves_lt b (RO.put_fix_body v vbody b0).
Proof.
  intros Hpres Hv k Hk.
  specialize (Hpres k Hk) as [Hlbl [Hsucc [Hfix Hbody]]].
  assert (Hneq : v <> k) by lia.
  unfold RO.put_fix_body; simpl.
  repeat split.
  - exact Hlbl.
  - exact Hsucc.
  - exact Hfix.
  - rewrite lookup_insert_ne by exact Hneq. exact Hbody.
Qed.

(** Successor/fix-ty closure w.r.t. current [b_next]. *)
Definition wf_builder (b : RO.builder) : Prop :=
  dom_lt b /\ closed_lt b (RO.b_next b).

Lemma wf_builder_empty : wf_builder RO.empty_builder.
Proof.
  split.
  - apply dom_lt_empty.
  - repeat split; intros; simpl in H; rewrite lookup_empty in H; discriminate.
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
  - destruct Hclosed as [Hsucc [Hfix Hbody]].
    destruct Hdom as [_ [Hdom_succ [Hdom_fix Hdom_body]]].
    split.
    + intros k succ Hk Hlt.
      unfold RO.fresh in Hk.
      simpl in Hk.
      assert (Hklt : k < RO.b_next b) by (eapply Hdom_succ; eauto).
      specialize (Hsucc k succ Hk Hklt) as Hclosed_succ.
      eapply Forall_impl; [exact Hclosed_succ|].
      intros w Hw.
      exact (Nat.lt_lt_succ_r _ _ Hw).
    + split.
      * intros k vA Hk Hlt.
        unfold RO.fresh in Hk.
        simpl in Hk.
        assert (Hklt : k < RO.b_next b) by (eapply Hdom_fix; eauto).
        specialize (Hfix k vA Hk Hklt) as HvAlt.
        exact (Nat.lt_lt_succ_r _ _ HvAlt).
      * intros k vbody Hk Hlt.
        unfold RO.fresh in Hk.
        simpl in Hk.
        assert (Hklt : k < RO.b_next b) by (eapply Hdom_body; eauto).
        specialize (Hbody k vbody Hk Hklt) as Hvlt.
        exact (Nat.lt_lt_succ_r _ _ Hvlt).
Qed.


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

Lemma preserves_lt_build_subst_chain_over
    (b : RO.builder) (us : list nat) (sv_tail : nat) (b0 : RO.builder) :
  preserves_lt b b0 ->
  RO.b_next b <= RO.b_next b0 ->
  preserves_lt b (snd (RO.build_subst_chain us sv_tail b0)).
Proof.
  revert b0.
  induction us as [|u us IH]; intro b0; intros Hpres Hle; simpl.
  - exact Hpres.
  - destruct (RO.build_subst_chain us sv_tail b0) as [sv_tail' b1] eqn:Hch.
    specialize (IH b0 Hpres Hle).
    rewrite Hch in IH. simpl in IH.
    pose proof (build_subst_chain_bnext_mono us sv_tail b0) as Hbmn.
    rewrite Hch in Hbmn. simpl in Hbmn.
    set (b2 := snd (RO.fresh b1)).
    pose proof (preserves_lt_fresh b1) as Hpres_fresh.
    assert (RO.b_next b <= RO.b_next b1) by lia.
    pose proof (preserves_lt_trans b b1 b2 IH Hpres_fresh ltac:(lia)) as Hpres2.
    subst b2.
    apply (preserves_lt_put_over b (snd (RO.fresh b1)) (RO.b_next b1)
             (RO.nSubstCons 0) [u; sv_tail'] Hpres2).
    lia.
Qed.

(** Compilation never overwrites existing vertices < old `b_next`. *)
Lemma compile_tm_list_preserves_lt_mutual :
  forall fuel,
    (forall ρ t b,
        preserves_lt b (snd (RO.compile_tm fuel ρ t b)))
    /\ (forall ρ ts b,
          preserves_lt b (snd (RO.compile_list fuel ρ ts b))).
Proof.
  induction fuel as [|fuel IH].
  - split.
    + intros ρ t b.
      cbn [RO.compile_tm].
      destruct (RO.fresh b) as [v b1] eqn:Hfr.
      pose proof (preserves_lt_fresh b) as Hpres1.
      rewrite Hfr in Hpres1. simpl in Hpres1.
      pose proof (fresh_fst_eq b) as Hv.
      rewrite Hfr in Hv. simpl in Hv. subst v.
      apply (preserves_lt_put_over b b1 (RO.b_next b) (RO.nVar 0) [] Hpres1).
      lia.
    + intros ρ ts b.
      cbn [RO.compile_list].
      apply preserves_lt_refl.
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
        pose proof (preserves_lt_fresh b) as Hpres1.
        rewrite Hfr in Hpres1. simpl in Hpres1.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b1 (RO.b_next b) (RO.nVar x) [] Hpres1).
        lia.
      * (* tSort *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (preserves_lt_fresh b) as Hpres1.
        rewrite Hfr in Hpres1. simpl in Hpres1.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b1 (RO.b_next b) (RO.nSort i) [] Hpres1).
        lia.
      * (* tPi *)
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b) as HpresA.
        rewrite HA in HpresA. simpl in HpresA.
        pose proof (compile_tm_bnext_mono fuel ρ A b) as Hb01.
        rewrite HA in Hb01. simpl in Hb01.
        destruct (RO.compile_tm fuel (None :: ρ) B b1) as [vB b2] eqn:HB.
        pose proof (IHtm (None :: ρ) B b1) as HpresB.
        rewrite HB in HpresB. simpl in HpresB.
        pose proof (compile_tm_bnext_mono fuel (None :: ρ) B b1) as Hb12.
        rewrite HB in Hb12. simpl in Hb12.
        pose proof (preserves_lt_trans b b1 b2 HpresA HpresB Hb01) as Hpres2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (preserves_lt_fresh b2) as Hpres_fresh.
        rewrite Hfr in Hpres_fresh. simpl in Hpres_fresh.
        assert (RO.b_next b <= RO.b_next b2) by lia.
        pose proof (preserves_lt_trans b b2 b3 Hpres2 Hpres_fresh ltac:(lia)) as Hpres3.
        pose proof (fresh_fst_eq b2) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b3 (RO.b_next b2) RO.nPi [vA; vB] Hpres3).
        lia.
      * (* tLam *)
        destruct (RO.compile_tm fuel ρ A b) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b) as HpresA.
        rewrite HA in HpresA. simpl in HpresA.
        pose proof (compile_tm_bnext_mono fuel ρ A b) as Hb01.
        rewrite HA in Hb01. simpl in Hb01.
        destruct (RO.compile_tm fuel (None :: ρ) t0 b1) as [vt b2] eqn:Ht0.
        pose proof (IHtm (None :: ρ) t0 b1) as HpresB.
        rewrite Ht0 in HpresB. simpl in HpresB.
        pose proof (compile_tm_bnext_mono fuel (None :: ρ) t0 b1) as Hb12.
        rewrite Ht0 in Hb12. simpl in Hb12.
        pose proof (preserves_lt_trans b b1 b2 HpresA HpresB Hb01) as Hpres2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (preserves_lt_fresh b2) as Hpres_fresh.
        rewrite Hfr in Hpres_fresh. simpl in Hpres_fresh.
        assert (RO.b_next b <= RO.b_next b2) by lia.
        pose proof (preserves_lt_trans b b2 b3 Hpres2 Hpres_fresh ltac:(lia)) as Hpres3.
        pose proof (fresh_fst_eq b2) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b3 (RO.b_next b2) RO.nLam [vA; vt] Hpres3).
        lia.
      * (* tApp *)
        destruct (RO.app_view (T.tApp t1 t2)) as [h args] eqn:Hv.
        destruct h;
          try solve [
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IHtm ρ t1 b) as Hpres1; rewrite H1 in Hpres1; simpl in Hpres1;
            pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hb01; rewrite H1 in Hb01; simpl in Hb01;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IHtm ρ t2 b1) as Hpres2; rewrite H2 in Hpres2; simpl in Hpres2;
            pose proof (compile_tm_bnext_mono fuel ρ t2 b1) as Hb12; rewrite H2 in Hb12; simpl in Hb12;
            pose proof (preserves_lt_trans b b1 b2 Hpres1 Hpres2 Hb01) as Hpresb2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (preserves_lt_fresh b2) as Hpres_fresh; rewrite Hfr in Hpres_fresh; simpl in Hpres_fresh;
            assert (RO.b_next b <= RO.b_next b2) by lia;
            pose proof (preserves_lt_trans b b2 b3 Hpresb2 Hpres_fresh ltac:(lia)) as Hpresb3;
            pose proof (fresh_fst_eq b2) as Hv0; rewrite Hfr in Hv0; simpl in Hv0; subst v;
            apply (preserves_lt_put_over b b3 (RO.b_next b2) RO.nApp [v1; v2] Hpresb3);
            lia].
        destruct (nth_error ρ x) as [[target|]|] eqn:Hnth;
          try solve [
            destruct (RO.compile_tm fuel ρ t1 b) as [v1 b1] eqn:H1;
            pose proof (IHtm ρ t1 b) as Hpres1; rewrite H1 in Hpres1; simpl in Hpres1;
            pose proof (compile_tm_bnext_mono fuel ρ t1 b) as Hb01; rewrite H1 in Hb01; simpl in Hb01;
            destruct (RO.compile_tm fuel ρ t2 b1) as [v2 b2] eqn:H2;
            pose proof (IHtm ρ t2 b1) as Hpres2; rewrite H2 in Hpres2; simpl in Hpres2;
            pose proof (compile_tm_bnext_mono fuel ρ t2 b1) as Hb12; rewrite H2 in Hb12; simpl in Hb12;
            pose proof (preserves_lt_trans b b1 b2 Hpres1 Hpres2 Hb01) as Hpresb2;
            destruct (RO.fresh b2) as [v b3] eqn:Hfr;
            pose proof (preserves_lt_fresh b2) as Hpres_fresh; rewrite Hfr in Hpres_fresh; simpl in Hpres_fresh;
            assert (RO.b_next b <= RO.b_next b2) by lia;
            pose proof (preserves_lt_trans b b2 b3 Hpresb2 Hpres_fresh ltac:(lia)) as Hpresb3;
            pose proof (fresh_fst_eq b2) as Hv0; rewrite Hfr in Hv0; simpl in Hv0; subst v;
            apply (preserves_lt_put_over b b3 (RO.b_next b2) RO.nApp [v1; v2] Hpresb3);
            lia].
        (* backlink case *)
        destruct (RO.compile_list fuel ρ args b) as [v_args b1] eqn:Hargs.
        pose proof (IHlist ρ args b) as Hpres_args.
        rewrite Hargs in Hpres_args. simpl in Hpres_args.
        pose proof (compile_list_bnext_mono fuel ρ args b) as Hb01.
        rewrite Hargs in Hb01. simpl in Hb01.
        destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfr1.
        pose proof (preserves_lt_fresh b1) as Hpres_fresh1.
        rewrite Hfr1 in Hpres_fresh1. simpl in Hpres_fresh1.
        pose proof (preserves_lt_trans b b1 b2 Hpres_args Hpres_fresh1 Hb01) as Hpres_b2.
        pose proof (fresh_fst_eq b1) as Hsv_nil.
        rewrite Hfr1 in Hsv_nil. simpl in Hsv_nil. subst sv_nil.
        set (b3 := RO.put (RO.b_next b1) (RO.nSubstNil 0) [] b2).
        pose proof (preserves_lt_put_over b b2 (RO.b_next b1) (RO.nSubstNil 0) [] Hpres_b2 ltac:(lia)) as Hpres_b3.
        pose proof (fresh_snd_next b1) as Hb2next.
        rewrite Hfr1 in Hb2next. simpl in Hb2next.
        assert (Hb_le_b3 : RO.b_next b <= RO.b_next b3).
        { unfold b3. simpl. rewrite Hb2next. lia. }
        destruct (RO.build_subst_chain v_args (RO.b_next b1) b3) as [sv b4] eqn:Hch.
        pose proof (preserves_lt_build_subst_chain_over b v_args (RO.b_next b1) b3 Hpres_b3 Hb_le_b3) as Hpres_b4.
        rewrite Hch in Hpres_b4. simpl in Hpres_b4.
        destruct (RO.fresh b4) as [v_back b5] eqn:Hfr2.
        pose proof (preserves_lt_fresh b4) as Hpres_fresh2.
        rewrite Hfr2 in Hpres_fresh2. simpl in Hpres_fresh2.
        assert (RO.b_next b <= RO.b_next b4) by (pose proof (build_subst_chain_bnext_mono v_args (RO.b_next b1) b3) as Hbmn; rewrite Hch in Hbmn; simpl in Hbmn; lia).
        pose proof (preserves_lt_trans b b4 b5 Hpres_b4 Hpres_fresh2 ltac:(lia)) as Hpres_b5.
        pose proof (fresh_fst_eq b4) as Hv_back.
        rewrite Hfr2 in Hv_back. simpl in Hv_back. subst v_back.
        apply (preserves_lt_put_over b b5 (RO.b_next b4) RO.nBack [target; sv] Hpres_b5).
        lia.
      * (* tFix *)
        destruct (RO.fresh b) as [v b0] eqn:Hfr.
        pose proof (preserves_lt_fresh b) as Hpres0.
        rewrite Hfr in Hpres0. simpl in Hpres0.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        pose proof (fresh_snd_next b) as Hb0next.
        rewrite Hfr in Hb0next. simpl in Hb0next.
        destruct (RO.compile_tm fuel ρ A b0) as [vA b1] eqn:HA.
        pose proof (IHtm ρ A b0) as HpresA.
        rewrite HA in HpresA. simpl in HpresA.
        pose proof (compile_tm_bnext_mono fuel ρ A b0) as Hb01.
        rewrite HA in Hb01. simpl in Hb01.
        pose proof (preserves_lt_trans b b0 b1 Hpres0 HpresA ltac:(lia)) as Hpres_b1.
        set (b1' := RO.put_fix_ty (RO.b_next b) vA b1).
        pose proof (preserves_lt_put_fix_ty_over b b1 (RO.b_next b) vA Hpres_b1 ltac:(lia)) as Hpres_b1'.
        destruct (RO.compile_tm fuel (Some (RO.b_next b) :: ρ) body b1') as [vbody b2] eqn:HB.
        pose proof (IHtm (Some (RO.b_next b) :: ρ) body b1') as HpresB.
        rewrite HB in HpresB. simpl in HpresB.
        pose proof (compile_tm_bnext_mono fuel (Some (RO.b_next b) :: ρ) body b1') as Hb12.
        rewrite HB in Hb12. simpl in Hb12.
        assert (RO.b_next b <= RO.b_next b1') by (subst b1'; simpl; lia).
        pose proof (preserves_lt_trans b b1' b2 Hpres_b1' HpresB ltac:(lia)) as Hpres_b2.
        apply (preserves_lt_put_over b b2 (RO.b_next b) (default (RO.nVar 0) (RO.b_label b2 !! vbody)) (default [] (RO.b_succ b2 !! vbody)) Hpres_b2).
        lia.
      * (* tInd *)
        destruct (RO.fresh b) as [v b1] eqn:Hfr.
        pose proof (preserves_lt_fresh b) as Hpres1.
        rewrite Hfr in Hpres1. simpl in Hpres1.
        pose proof (fresh_fst_eq b) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b1 (RO.b_next b) (RO.nInd I) [] Hpres1).
        lia.
      * (* tRoll *)
        destruct (RO.compile_list fuel ρ params b) as [vps b1] eqn:Hps.
        pose proof (IHlist ρ params b) as Hpres1.
        rewrite Hps in Hpres1. simpl in Hpres1.
        pose proof (compile_list_bnext_mono fuel ρ params b) as Hb01.
        rewrite Hps in Hb01. simpl in Hb01.
        destruct (RO.compile_list fuel ρ recs b1) as [vrs b2] eqn:Hrs.
        pose proof (IHlist ρ recs b1) as Hpres2.
        rewrite Hrs in Hpres2. simpl in Hpres2.
        pose proof (compile_list_bnext_mono fuel ρ recs b1) as Hb12.
        rewrite Hrs in Hb12. simpl in Hb12.
        pose proof (preserves_lt_trans b b1 b2 Hpres1 Hpres2 Hb01) as Hpresb2.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        pose proof (preserves_lt_fresh b2) as Hpres_fresh.
        rewrite Hfr in Hpres_fresh. simpl in Hpres_fresh.
        assert (RO.b_next b <= RO.b_next b2) by lia.
        pose proof (preserves_lt_trans b b2 b3 Hpresb2 Hpres_fresh ltac:(lia)) as Hpresb3.
        pose proof (fresh_fst_eq b2) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b3 (RO.b_next b2)
                 (RO.nRoll I c (length vps) (length vrs)) (vps ++ vrs) Hpresb3).
        lia.
      * (* tCase *)
        destruct (RO.compile_tm fuel ρ scrut b) as [vscrut b1] eqn:Hs.
        pose proof (IHtm ρ scrut b) as Hpres1.
        rewrite Hs in Hpres1. simpl in Hpres1.
        pose proof (compile_tm_bnext_mono fuel ρ scrut b) as Hb01.
        rewrite Hs in Hb01. simpl in Hb01.
        destruct (RO.compile_tm fuel ρ C b1) as [vC b2] eqn:Hc.
        pose proof (IHtm ρ C b1) as Hpres2.
        rewrite Hc in Hpres2. simpl in Hpres2.
        pose proof (preserves_lt_trans b b1 b2 Hpres1 Hpres2 Hb01) as Hpresb2.
        pose proof (compile_tm_bnext_mono fuel ρ C b1) as Hb12.
        rewrite Hc in Hb12. simpl in Hb12.
        assert (Htlt2 : RO.b_next b <= RO.b_next b2) by lia.
        destruct (RO.compile_list fuel ρ brs b2) as [vbrs b3] eqn:Hbrs.
        pose proof (IHlist ρ brs b2) as Hpres3.
        rewrite Hbrs in Hpres3. simpl in Hpres3.
        pose proof (compile_list_bnext_mono fuel ρ brs b2) as Hb23.
        rewrite Hbrs in Hb23. simpl in Hb23.
        pose proof (preserves_lt_trans b b2 b3 Hpresb2 Hpres3 ltac:(lia)) as Hpresb3.
        destruct (RO.fresh b3) as [v b4] eqn:Hfr.
        pose proof (preserves_lt_fresh b3) as Hpres_fresh.
        rewrite Hfr in Hpres_fresh. simpl in Hpres_fresh.
        assert (RO.b_next b <= RO.b_next b3) by lia.
        pose proof (preserves_lt_trans b b3 b4 Hpresb3 Hpres_fresh ltac:(lia)) as Hpresb4.
        pose proof (fresh_fst_eq b3) as Hv.
        rewrite Hfr in Hv. simpl in Hv. subst v.
        apply (preserves_lt_put_over b b4 (RO.b_next b3)
                 (RO.nCase I (length vbrs)) ([vscrut; vC] ++ vbrs) Hpresb4).
        lia.
    + intros ρ ts b.
      cbn [RO.compile_list].
      destruct ts as [|t ts].
      * exact (preserves_lt_refl b).
      * destruct (RO.compile_tm fuel ρ t b) as [v b1] eqn:Ht.
        pose proof (IHtm ρ t b) as Hpres1.
        rewrite Ht in Hpres1. simpl in Hpres1.
        pose proof (compile_tm_bnext_mono fuel ρ t b) as Hb01.
        rewrite Ht in Hb01. simpl in Hb01.
        destruct (RO.compile_list fuel ρ ts b1) as [vs b2] eqn:Hts.
        pose proof (IHlist ρ ts b1) as Hpres2.
        rewrite Hts in Hpres2. simpl in Hpres2.
        exact (preserves_lt_trans b b1 b2 Hpres1 Hpres2 Hb01).
Qed.

Lemma compile_tm_preserves_lt
    (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  preserves_lt b (snd (RO.compile_tm fuel ρ t b)).
Proof.
  exact (proj1 (compile_tm_list_preserves_lt_mutual fuel) ρ t b).
Qed.

Lemma compile_list_preserves_lt
    (fuel : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  preserves_lt b (snd (RO.compile_list fuel ρ ts b)).
Proof.
  exact (proj2 (compile_tm_list_preserves_lt_mutual fuel) ρ ts b).
Qed.


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
  intros [Hsucc [Hfix Hbody]] Hv Hsuccs.
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
  - split.
    + intros k vA Hk Hklt.
      unfold RO.put in Hk. simpl in Hk.
      exact (Hfix k vA Hk Hklt).
    + intros k vbody Hk Hklt.
      unfold RO.put in Hk. simpl in Hk.
      exact (Hbody k vbody Hk Hklt).
Qed.

Lemma closed_lt_fresh (b : RO.builder) :
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  closed_lt (snd (RO.fresh b)) (RO.b_next (snd (RO.fresh b))).
Proof.
  intros Hdom Hcl.
  unfold RO.fresh.
  simpl.
  destruct Hcl as [Hsucc [Hfix Hbody]].
  destruct Hdom as [_ [Hdom_succ [Hdom_fix Hdom_body]]].
  split.
  - intros k succ Hk Hlt.
    assert (k < RO.b_next b) by (eapply Hdom_succ; eauto).
    pose proof (Hsucc k succ Hk H) as Hfor.
    eapply Forall_impl; [exact Hfor|].
    intros w Hw.
    exact (Nat.lt_lt_succ_r _ _ Hw).
  - split.
    + intros k vA Hk Hlt.
      assert (k < RO.b_next b) by (eapply Hdom_fix; eauto).
      pose proof (Hfix k vA Hk H) as HvA_lt.
      exact (Nat.lt_lt_succ_r _ _ HvA_lt).
    + intros k vbody Hk Hlt.
      assert (k < RO.b_next b) by (eapply Hdom_body; eauto).
      pose proof (Hbody k vbody Hk H) as Hv_lt.
      exact (Nat.lt_lt_succ_r _ _ Hv_lt).
Qed.

Lemma closed_lt_put_fix_ty_over (b : RO.builder) (n k vA : nat) :
  closed_lt b n ->
  k < n ->
  vA < n ->
  closed_lt (RO.put_fix_ty k vA b) n.
Proof.
  intros [Hsucc [Hfix Hbody]] Hklt HvA.
  split.
  - intros k0 succ Hk0 Hlt.
    unfold RO.put_fix_ty in Hk0. simpl in Hk0.
    exact (Hsucc k0 succ Hk0 Hlt).
  - split.
    + intros k0 vA0 Hk0 Hlt.
      unfold RO.put_fix_ty in Hk0. simpl in Hk0.
      destruct (decide (k0 = k)) as [->|Hne].
      * try (rewrite lookup_insert in Hk0).
        destruct (decide (k = k)) as [_|Hfalse].
        { simpl in Hk0. inversion Hk0; subst. exact HvA. }
        { exfalso; apply Hfalse; reflexivity. }
      * destruct (decide (k = k0)) as [Heq|Hneq].
        { exfalso; apply Hne; symmetry; exact Heq. }
        { try (rewrite lookup_insert_ne in Hk0 by exact Hneq).
          simpl in Hk0.
          exact (Hfix k0 vA0 Hk0 Hlt). }
    + intros k0 vbody Hk0 Hlt.
      unfold RO.put_fix_ty in Hk0. simpl in Hk0.
      exact (Hbody k0 vbody Hk0 Hlt).
Qed.

Lemma closed_lt_put_fix_body_over (b : RO.builder) (n k vbody : nat) :
  closed_lt b n ->
  k < n ->
  vbody < n ->
  closed_lt (RO.put_fix_body k vbody b) n.
Proof.
  intros [Hsucc [Hfix Hbody]] Hklt Hvbody.
  split.
  - intros k0 succ Hk0 Hlt.
    unfold RO.put_fix_body in Hk0. simpl in Hk0.
    exact (Hsucc k0 succ Hk0 Hlt).
  - split.
    + intros k0 vA0 Hk0 Hlt.
      unfold RO.put_fix_body in Hk0. simpl in Hk0.
      exact (Hfix k0 vA0 Hk0 Hlt).
    + intros k0 vbody0 Hk0 Hlt.
      unfold RO.put_fix_body in Hk0. simpl in Hk0.
      destruct (decide (k0 = k)) as [->|Hne].
      * rewrite lookup_insert in Hk0.
        destruct (decide (k = k)) as [_|Hfalse].
        { simpl in Hk0. inversion Hk0; subst. exact Hvbody. }
        { exfalso; apply Hfalse; reflexivity. }
      * destruct (decide (k = k0)) as [Heq|Hneq].
        { exfalso; apply Hne; symmetry; exact Heq. }
        { rewrite lookup_insert_ne in Hk0 by exact Hneq.
          simpl in Hk0.
          exact (Hbody k0 vbody0 Hk0 Hlt). }
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
        { simpl in Hk.
          inversion Hk; subst; clear Hk.
          constructor.
          - (* u < b_next b2 *) lia.
          - constructor; [lia|constructor]. }
        { exfalso; apply Hfalse; reflexivity. }
      * destruct (decide (RO.b_next b1 = k)) as [Heq|Hneq].
        { exfalso; apply Hne; symmetry; exact Heq. }
        { try (rewrite lookup_insert_ne in Hk by exact Hneq).
          simpl in Hk.
          destruct Hcl2 as [Hsucc2 _].
          exact (Hsucc2 k succ Hk Hklt). }
    + split.
      * intros k vA Hk Hklt.
        unfold RO.put in Hk. simpl in Hk.
        destruct Hcl2 as [_ [Hfix2 _]].
        exact (Hfix2 k vA Hk Hklt).
      * intros k vbody Hk Hklt.
        unfold RO.put in Hk. simpl in Hk.
        destruct Hcl2 as [_ [_ Hbody2]].
        exact (Hbody2 k vbody Hk Hklt).
Qed.

Section PutLemmas.
  Lemma lookup_node_put_eq (b : RO.builder) (v : nat) (lbl : RO.node) (succs : list nat) :
    EX.lookup_node (RO.put v lbl succs b) v = lbl.
  Proof.
    unfold EX.lookup_node, RO.put.
    simpl.
    try rewrite lookup_insert.
    try (rewrite decide_True by reflexivity).
    simpl.
    reflexivity.
  Qed.

  Lemma lookup_succ_put_eq (b : RO.builder) (v : nat) (lbl : RO.node) (succs : list nat) :
    EX.lookup_succ (RO.put v lbl succs b) v = succs.
  Proof.
    unfold EX.lookup_succ, RO.put.
    simpl.
    try rewrite lookup_insert.
    try (rewrite decide_True by reflexivity).
    simpl.
    reflexivity.
  Qed.
End PutLemmas.

Section ExtractExt.
  Context (b b' : RO.builder) (n : nat).
  Hypothesis Hagree :
    forall k,
      k < n ->
      b'.(RO.b_label) !! k = b.(RO.b_label) !! k
      /\ b'.(RO.b_succ) !! k = b.(RO.b_succ) !! k
      /\ b'.(RO.b_fix_ty) !! k = b.(RO.b_fix_ty) !! k
      /\ b'.(RO.b_fix_body) !! k = b.(RO.b_fix_body) !! k.
  Hypothesis Hclosed : closed_lt b n.

  Lemma lookup_node_agree (v : nat) : v < n -> EX.lookup_node b v = EX.lookup_node b' v.
  Proof using Hagree.
    intro Hv.
    unfold EX.lookup_node.
    destruct (Hagree v Hv) as [Hl _].
    rewrite Hl.
    reflexivity.
  Qed.

  Lemma lookup_succ_agree (v : nat) : v < n -> EX.lookup_succ b v = EX.lookup_succ b' v.
  Proof using Hagree.
    intro Hv.
    unfold EX.lookup_succ.
    destruct (Hagree v Hv) as [_ [Hs _]].
    rewrite Hs.
    reflexivity.
  Qed.

  Lemma fix_ty_agree (v : nat) : v < n -> RO.b_fix_ty b !! v = RO.b_fix_ty b' !! v.
  Proof using Hagree.
    intro Hv.
    destruct (Hagree v Hv) as [_ [_ [Hf _]]].
    exact (eq_sym Hf).
  Qed.

  Lemma fix_body_agree (v : nat) : v < n -> RO.b_fix_body b !! v = RO.b_fix_body b' !! v.
  Proof using Hagree.
    intro Hv.
    destruct (Hagree v Hv) as [_ [_ [_ Hb]]].
    exact (eq_sym Hb).
  Qed.

  Lemma extract_ext (fuel : nat) :
    (forall ρ v, v < n -> EX.extract_v fuel b ρ v = EX.extract_v fuel b' ρ v)
    /\ (forall ρ v, v < n -> EX.extract_node fuel b ρ v = EX.extract_node fuel b' ρ v)
    /\ (forall ρ sv, sv < n -> EX.subst_args fuel b ρ sv = EX.subst_args fuel b' ρ sv)
    /\ (forall ρ vs, Forall (fun w => w < n) vs ->
          EX.extract_list EX.extract_v fuel b ρ vs =
          EX.extract_list EX.extract_v fuel b' ρ vs).
  Proof using Hagree Hclosed.
    induction fuel as [|fuel IH]; simpl.
    - repeat split; intros; reflexivity.
    - destruct IH as [IHv [IHn [IHs IHl]]].
      assert (HlistS : forall ρ vs,
                Forall (fun w => w < n) vs ->
                EX.extract_list EX.extract_v (S fuel) b ρ vs =
                EX.extract_list EX.extract_v (S fuel) b' ρ vs).
      { intros ρ0 vs Hvs.
        destruct vs as [|w ws]; simpl; [reflexivity|].
        inversion Hvs as [|? ? Hw Hws]; subst.
        rewrite (IHv ρ0 w Hw).
        f_equal.
        exact (IHl ρ0 ws Hws).
      }
      assert (Htake : forall k xs,
                Forall (fun w => w < n) xs -> Forall (fun w => w < n) (take k xs)).
      { induction k as [|k IHk]; intros xs Hxs; simpl; [constructor|].
        destruct xs as [|x xs]; simpl; [constructor|].
        inversion Hxs; subst.
        constructor; [assumption|].
        apply IHk. assumption.
      }
      assert (Hdrop : forall k xs,
                Forall (fun w => w < n) xs -> Forall (fun w => w < n) (drop k xs)).
      { induction k as [|k IHk]; intros xs Hxs; simpl.
        - exact Hxs.
        - destruct xs as [|x xs]; simpl; [constructor|].
          inversion Hxs; subst.
          apply IHk. assumption.
      }
      repeat split.
      + (* extract_v *)
        intros ρ0 v Hv.
        simpl.
        destruct (ρ0 !! v) as [k|] eqn:Hρ; [reflexivity|].
        rewrite <- (fix_ty_agree v Hv).
        destruct (RO.b_fix_ty b !! v) as [vA|] eqn:Hfix.
        * destruct Hclosed as [_ [Hfixval Hbodyval]].
          assert (HvA : vA < n) by (eapply Hfixval; eauto).
          rewrite (IHv ρ0 vA HvA).
          (* body root may be recorded; if so we must agree and recurse on it *)
          rewrite <- (fix_body_agree v Hv).
          destruct (RO.b_fix_body b !! v) as [vbody|] eqn:Hfb.
          { assert (Hvbody : vbody < n) by (eapply Hbodyval; eauto).
            rewrite (IHv (<[v := 0]> (EX.env_shift ρ0)) vbody Hvbody).
            reflexivity. }
          rewrite (IHn (<[v := 0]> (EX.env_shift ρ0)) v Hv).
          reflexivity.
        * rewrite (IHn ρ0 v Hv). reflexivity.
      + (* extract_node *)
        intros ρ0 v Hv.
        simpl.
        rewrite <- (lookup_node_agree v Hv).
        destruct (EX.lookup_node b v) eqn:Hlbl; simpl; try reflexivity.
        * (* nPi *)
          rewrite <- (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|vA [|vB xs]] eqn:Hsu; try reflexivity.
          destruct xs; try reflexivity.
          unfold EX.lookup_succ in Hsu.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in Hsu; try discriminate.
          inversion Hsu; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [vA; vB] Hsv Hv).
          inversion Hsucc as [|? ? HvA Hsucc']; subst.
          inversion Hsucc' as [|? ? HvB _]; subst.
          rewrite (IHv ρ0 vA HvA).
          rewrite (IHv (EX.env_shift ρ0) vB HvB).
          reflexivity.
        * (* nLam *)
          rewrite <- (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|vA [|vt xs]] eqn:Hsu; try reflexivity.
          destruct xs; try reflexivity.
          unfold EX.lookup_succ in Hsu.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in Hsu; try discriminate.
          inversion Hsu; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [vA; vt] Hsv Hv).
          inversion Hsucc as [|? ? HvA Hsucc']; subst.
          inversion Hsucc' as [|? ? Hvt _]; subst.
          rewrite (IHv ρ0 vA HvA).
          rewrite (IHv (EX.env_shift ρ0) vt Hvt).
          reflexivity.
        * (* nApp *)
          rewrite <- (lookup_succ_agree v Hv).
          destruct (EX.lookup_succ b v) as [|vf [|va xs]] eqn:Hsu; try reflexivity.
          destruct xs; try reflexivity.
          unfold EX.lookup_succ in Hsu.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl in Hsu; try discriminate.
          inversion Hsu; subst succ.
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v [vf; va] Hsv Hv).
          inversion Hsucc as [|? ? Hvf Hsucc']; subst.
          inversion Hsucc' as [|? ? Hva _]; subst.
          rewrite (IHv ρ0 vf Hvf).
          rewrite (IHv ρ0 va Hva).
          reflexivity.
        * (* nRoll *)
          rewrite <- (lookup_succ_agree v Hv).
          unfold EX.lookup_succ.
          destruct (RO.b_succ b !! v) as [succ|] eqn:Hsv; simpl.
          { destruct Hclosed as [Hsucc _].
            pose proof (Hsucc v succ Hsv Hv) as Hxs.
            set (ps := take nparams succ).
            set (rs := drop nparams succ).
            assert (Hps : Forall (fun w => w < n) ps).
            { subst ps. exact (Htake nparams succ Hxs). }
            assert (Hrs : Forall (fun w => w < n) rs).
            { subst rs. exact (Hdrop nparams succ Hxs). }
            simpl.
            f_equal.
            - destruct ps as [|p ps']; simpl; [reflexivity|].
              inversion Hps as [|? ? Hp Hps']; subst.
              rewrite (IHv ρ0 p Hp).
              f_equal.
              exact (IHl ρ0 ps' Hps').
            - destruct rs as [|r rs']; simpl; [reflexivity|].
              inversion Hrs as [|? ? Hr Hrs']; subst.
              rewrite (IHv ρ0 r Hr).
              f_equal.
              exact (IHl ρ0 rs' Hrs'). }
          { simpl. rewrite take_nil, drop_nil. reflexivity. }
        * (* nCase *)
          rewrite <- (lookup_succ_agree v Hv).
          unfold EX.lookup_succ.
          destruct (RO.b_succ b !! v) as [xs|] eqn:Hsv; simpl; [|reflexivity].
          destruct Hclosed as [Hsucc _].
          specialize (Hsucc v xs Hsv Hv).
          destruct xs as [|vscrut xs]; [reflexivity|].
          destruct xs as [|vC brs]; [reflexivity|].
          inversion Hsucc as [|? ? Hscrut Hsucc']; subst.
          inversion Hsucc' as [|? ? HC Hbrs]; subst.
          rewrite (IHv ρ0 vscrut Hscrut).
          rewrite (IHv ρ0 vC HC).
          set (brs' := take nbrs brs).
          assert (Hbrs' : Forall (fun w => w < n) brs').
          { subst brs'. exact (Htake nbrs brs Hbrs). }
          simpl.
          f_equal.
          destruct brs' as [|p ps]; simpl; [reflexivity|].
          inversion Hbrs' as [|? ? Hp Hps]; subst.
          rewrite (IHv ρ0 p Hp).
          f_equal.
          exact (IHl ρ0 ps Hps).
        * (* nBack *)
          rewrite <- (lookup_succ_agree v Hv).
          unfold EX.lookup_succ.
          destruct (RO.b_succ b !! v) as [xs|] eqn:Hsv; simpl; [|reflexivity].
          destruct xs as [|tgt xs]; [reflexivity|].
          destruct xs as [|sv xs]; [reflexivity|].
          destruct xs as [|? ?]; [|reflexivity].
          destruct (ρ0 !! tgt); try reflexivity.
          destruct Hclosed as [Hsucc _].
          pose proof (Hsucc v [tgt; sv] Hsv Hv) as Hsvs.
          inversion Hsvs as [|? ? Htgt Hsvs']; subst.
          inversion Hsvs' as [|? ? Hsv_lt _]; subst.
          rewrite (IHs ρ0 sv Hsv_lt).
          reflexivity.
      + (* subst_args *)
        intros ρ0 sv Hsv.
        simpl.
        rewrite <- (lookup_node_agree sv Hsv).
        destruct (EX.lookup_node b sv); try reflexivity.
        * (* nSubstCons *)
          rewrite <- (lookup_succ_agree sv Hsv).
          unfold EX.lookup_succ.
          destruct (RO.b_succ b !! sv) as [xs|] eqn:Hsvs; simpl; [|reflexivity].
          destruct xs as [|u xs]; [reflexivity|].
          destruct xs as [|sv_tail xs]; [reflexivity|].
          destruct xs as [|? ?]; [|reflexivity].
          destruct Hclosed as [Hsucc _].
          pose proof (Hsucc sv [u; sv_tail] Hsvs Hsv) as Hfor2.
          inversion Hfor2 as [|? ? Hu_lt Hfor2']; subst.
          inversion Hfor2' as [|? ? Htail_lt _]; subst.
          rewrite (IHv ρ0 u Hu_lt).
          rewrite (IHs ρ0 sv_tail Htail_lt).
          reflexivity.
       + (* extract_list *)
         exact HlistS.
  Qed.
End ExtractExt.

(* Convenience wrapper: instantiate `extract_ext` at a fixed environment `ρ`. *)
Lemma extract_ext_inst
    (b b' : RO.builder) (ρ : EX.fix_env) (n fuel : nat)
    (Hagree : forall k,
        k < n ->
        b'.(RO.b_label) !! k = b.(RO.b_label) !! k
        /\ b'.(RO.b_succ) !! k = b.(RO.b_succ) !! k
        /\ b'.(RO.b_fix_ty) !! k = b.(RO.b_fix_ty) !! k
        /\ b'.(RO.b_fix_body) !! k = b.(RO.b_fix_body) !! k)
    (Hclosed : closed_lt b n) :
  (forall v, v < n -> EX.extract_v fuel b ρ v = EX.extract_v fuel b' ρ v)
  /\ (forall v, v < n -> EX.extract_node fuel b ρ v = EX.extract_node fuel b' ρ v)
  /\ (forall sv, sv < n -> EX.subst_args fuel b ρ sv = EX.subst_args fuel b' ρ sv).
Proof.
  pose proof (@extract_ext b b' n Hagree Hclosed fuel) as [Hexv [Hexn [Hexs _]]].
  repeat split.
  - intros v Hv. exact (Hexv ρ v Hv).
  - intros v Hv. exact (Hexn ρ v Hv).
  - intros sv Hv. exact (Hexs ρ sv Hv).
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
  revert fuel b.
  induction us as [|u us IH]; intros fuel b; intros Hdom Hcl Hsv Hlbl Hsucc Hfor; simpl.
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
    unfold RO.fresh.
    simpl.
    set (sv_head := RO.b_next b1).
    set (b2 :=
           {| RO.b_next := S sv_head;
              RO.b_label := RO.b_label b1;
              RO.b_succ := RO.b_succ b1;
              RO.b_fix_ty := RO.b_fix_ty b1;
              RO.b_fix_body := RO.b_fix_body b1 |}).
    set (b3 := RO.put sv_head (RO.nSubstCons 0) [u; sv_tail] b2).
    destruct fuel as [|fuel']; simpl; auto.
    specialize (IH fuel' b Hdom Hcl Hsv Hlbl Hsucc Hfor').
    rewrite Hch in IH.
    unfold EX.lookup_node, EX.lookup_succ.
    unfold b3. simpl.
    rewrite lookup_insert.
    rewrite decide_True by reflexivity.
    rewrite lookup_insert.
    rewrite decide_True by reflexivity.
    simpl.
    fold b3.

    assert (Hagree : forall k,
              k < sv_head ->
              b3.(RO.b_label) !! k = b1.(RO.b_label) !! k
              /\ b3.(RO.b_succ) !! k = b1.(RO.b_succ) !! k
              /\ b3.(RO.b_fix_ty) !! k = b1.(RO.b_fix_ty) !! k
              /\ b3.(RO.b_fix_body) !! k = b1.(RO.b_fix_body) !! k).
    { intros k Hk.
      unfold b3, RO.put.
      simpl.
      assert (k <> sv_head) by lia.
      repeat split; try reflexivity; rewrite lookup_insert_ne; auto.
    }

    pose proof (@extract_ext b1 b3 sv_head Hagree Hcl1 fuel') as [Hexv [Hexn [Hexs _]]].

    assert (Htail_lt : sv_tail < sv_head).
    { pose proof (build_subst_chain_root_lt us sv_nil b Hsv) as Htail.
      rewrite Hch in Htail. simpl in Htail.
      unfold sv_head. lia. }

    rewrite <- (Hexs ρ sv_tail Htail_lt).
    rewrite IH.
    clear IH.
    f_equal.

    assert (Hvs_lt : Forall (fun x => x < sv_head) us).
    { pose proof (build_subst_chain_bnext_mono us sv_nil b) as Hbmn.
      rewrite Hch in Hbmn. simpl in Hbmn.
      eapply Forall_impl; [exact Hfor'|].
      intros x Hx.
      unfold sv_head.
      eapply Nat.lt_le_trans; [exact Hx|].
      exact Hbmn. }

    clear Hexv Hexn Hexs.
    clear Hfor Hu Hfor' Hch.
    revert us Hvs_lt.
    induction fuel' as [|fuel'' IHfuel]; intros us0 Hvs_lt0; simpl; [reflexivity|].
    destruct us0 as [|w ws]; [reflexivity|].
    inversion Hvs_lt0 as [|? ? Hw Hws]; subst.
    pose proof (@extract_ext b1 b3 sv_head Hagree Hcl1 fuel'') as [Hexv' [Hexn' [Hexs' _]]].
    rewrite (Hexv' ρ w Hw).
    f_equal.
    apply IHfuel.
    exact Hws.
Qed.

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

(** Compilation/extraction correctness.

    This is the key lemma needed for the read-off / extract round-trip.
*)
Definition list_max_size (ts : list T.tm) : nat :=
  fold_right Nat.max 0 (map T.size ts).

Definition list_size (ts : list T.tm) : nat :=
  (* `ReadOff.compile_list` decrements fuel by 1 per list cell, so the i-th element
     is compiled with fuel `fuel - (i+1)`.

     A sufficient bound is:
     - enough steps to traverse the list (`length ts`)
     - plus enough fuel for the largest element (`S (max size)`), so that even the
       last element still has at least `S (T.size u)` fuel available.

     This bound is intentionally *not* a sum of element sizes.
  *)
  match ts with
  | [] => 0
  | _ => length ts + S (list_max_size ts)
  end.

Lemma size_ge_1 (t : T.tm) : 1 <= T.size t.
Proof.
  induction t; cbn [T.size]; lia.
Qed.

Lemma list_max_size_le_sum_sizes (ts : list T.tm) :
  list_max_size ts <= fold_right (fun u n => T.size u + n) 0 ts.
Proof.
  induction ts as [|t ts IH].
  - cbn [list_max_size]. lia.
  - cbn [list_max_size].
    cbn [map].
    cbn [fold_right].
    (* max (size t) (max_size ts) <= size t + sum ts *)
    apply Nat.max_lub.
    + lia.
    + eapply Nat.le_trans; [exact IH|]. lia.
Qed.

Lemma size_apps_tm (h : T.tm) (us : list T.tm) :
  T.size (apps_tm h us) = T.size h + length us + fold_right (fun u n => T.size u + n) 0 us.
Proof.
  revert h.
  induction us as [|u us IH]; intros h.
  - cbn [apps_tm]. cbn [length fold_right]. lia.
  - cbn [apps_tm].
    specialize (IH (T.tApp h u)).
    rewrite IH.
    cbn [T.size length fold_right].
    lia.
Qed.

Lemma list_size_le_size_apps_tm (h : T.tm) (us : list T.tm) :
  list_size us <= T.size (apps_tm h us).
Proof.
  destruct us as [|u us].
  - cbn [list_size apps_tm].
    pose proof (size_ge_1 h).
    lia.
  - cbn [list_size].
    rewrite size_apps_tm.
    (* list_max_size (u::us) <= sum sizes (u::us) *)
    assert (Hmax : list_max_size (u :: us) <= fold_right (fun u0 n => T.size u0 + n) 0 (u :: us)).
    { apply list_max_size_le_sum_sizes. }
    pose proof (size_ge_1 h).
    lia.
Qed.

(** Fuel cost model for extraction.

    `EX.extract_v` consumes one unit of fuel before delegating to `extract_node`.
    `extract_node` consumes one unit of fuel before recursing into children.
    List-producing extractors (`EX.extract_list` / `EX.subst_args`) additionally
    consume one unit of fuel per list cell.

    The functions below over-approximate the fuel required to extract a given
    term/list *without* changing the result.
*)
Fixpoint fuel_cost_tm (t : T.tm) : nat :=
  match t with
  | T.tVar _ => 2
  | T.tSort _ => 2
  | T.tInd _ => 2
  | T.tPi A B => 2 + fuel_cost_tm A + fuel_cost_tm B
  | T.tLam A t => 2 + fuel_cost_tm A + fuel_cost_tm t
  | T.tApp t u => 2 + fuel_cost_tm t + fuel_cost_tm u
  | T.tFix A t => 2 + fuel_cost_tm A + fuel_cost_tm t
  | T.tRoll _ _ params recs =>
      2
      + fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 params
      + fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 recs
  | T.tCase _ scrut C brs =>
      2
      + fuel_cost_tm scrut
      + fuel_cost_tm C
      + fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 brs
  end.

Definition fuel_cost_list (ts : list T.tm) : nat :=
  fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 ts.

Lemma fuel_cost_list_nil : fuel_cost_list [] = 0.
Proof. reflexivity. Qed.

Lemma fuel_cost_list_cons (t : T.tm) (ts : list T.tm) :
  fuel_cost_list (t :: ts) = 1 + fuel_cost_tm t + fuel_cost_list ts.
Proof. reflexivity. Qed.

Definition fuel_cost_node (t : T.tm) : nat := Nat.pred (fuel_cost_tm t).

Lemma app_view_apps_tm (t : T.tm) (us : list T.tm) :
  RO.app_view (apps_tm t us) =
    let '(h, args) := RO.app_view t in (h, args ++ us).
Proof.
  revert t.
  induction us as [|u us IH]; intros t; simpl.
  - destruct (RO.app_view t) as [h args].
    simpl. rewrite app_nil_r. reflexivity.
  - specialize (IH (T.tApp t u)).
    rewrite IH.
    rewrite RO.app_view_tApp.
    destruct (RO.app_view t) as [h args] eqn:Hview.
    simpl.
    f_equal.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

Lemma apps_tm_inj (h : T.tm) (xs ys : list T.tm) :
  RO.app_view h = (h, []) ->
  apps_tm h xs = apps_tm h ys ->
  xs = ys.
Proof.
  intros Hh Heq.
  apply (f_equal RO.app_view) in Heq.
  rewrite (app_view_apps_tm h xs) in Heq.
  rewrite (app_view_apps_tm h ys) in Heq.
  rewrite Hh in Heq.
  simpl in Heq.
  inversion Heq. reflexivity.
Qed.


Lemma two_mul_succ (n : nat) : 2 * S n = S (S (2 * n)).
Proof. lia. Qed.

Local Opaque Nat.mul.
Local Opaque EX.lookup_node EX.lookup_succ.

(** Adequacy: fuel_cost is always at least 2 (for leaf constructors). *)
Lemma fuel_cost_tm_ge_2 (t : T.tm) : 2 <= fuel_cost_tm t.
Proof.
  destruct t; cbn [fuel_cost_tm]; lia.
Qed.

(** Adequacy bookkeeping lemmas for each constructor. *)

Lemma fuel_cost_tPi_subterms (A B : T.tm) (fuelE : nat) :
  fuelE >= fuel_cost_tm (T.tPi A B) ->
  fuelE - 2 >= fuel_cost_tm A /\ fuelE - 2 >= fuel_cost_tm B.
Proof.
  cbn [fuel_cost_tm]. lia.
Qed.

Lemma fuel_cost_tLam_subterms (A t : T.tm) (fuelE : nat) :
  fuelE >= fuel_cost_tm (T.tLam A t) ->
  fuelE - 2 >= fuel_cost_tm A /\ fuelE - 2 >= fuel_cost_tm t.
Proof.
  cbn [fuel_cost_tm]. lia.
Qed.

Lemma fuel_cost_tApp_subterms (t u : T.tm) (fuelE : nat) :
  fuelE >= fuel_cost_tm (T.tApp t u) ->
  fuelE - 2 >= fuel_cost_tm t /\ fuelE - 2 >= fuel_cost_tm u.
Proof.
  cbn [fuel_cost_tm]. lia.
Qed.

Lemma fuel_cost_tFix_subterms (A t : T.tm) (fuelE : nat) :
  fuelE >= fuel_cost_tm (T.tFix A t) ->
  fuelE - 2 >= fuel_cost_tm A /\ fuelE - 2 >= fuel_cost_tm t.
Proof.
  cbn [fuel_cost_tm]. lia.
Qed.

Lemma fuel_cost_list_subterms (t : T.tm) (ts : list T.tm) (fuelE : nat) :
  fuelE >= fuel_cost_list (t :: ts) ->
  fuelE - 1 >= fuel_cost_tm t /\ fuelE - 1 >= fuel_cost_list ts.
Proof.
  unfold fuel_cost_list.
  simpl.
  lia.
Qed.

Lemma fuel_cost_apps_tm_ge (t : T.tm) (us : list T.tm) :
  fuel_cost_tm (apps_tm t us) >= fuel_cost_tm t + fuel_cost_list us.
Proof.
  revert t.
  induction us as [|u us IH]; intros t.
  - cbn [apps_tm].
    unfold fuel_cost_list.
    simpl.
    lia.
  - cbn [apps_tm].
    specialize (IH (T.tApp t u)).
    unfold fuel_cost_list in *.
    simpl in *.
    cbn [fuel_cost_tm] in IH.
    lia.
Qed.

(** Core adequacy unfolding lemma: if we have enough fuel (>= 2), we can unfold
    `extract_v` and `extract_node` deterministically by destructing the fuel term. *)

Lemma extract_v_unfold_ge2
    (fuelE : nat) (b : RO.builder) (ρ : EX.fix_env) (v : nat) :
  fuelE >= 2 ->
  EX.extract_v fuelE b ρ v =
    match ρ !! v with
    | None =>
        match RO.b_fix_ty b !! v with
        | Some vA =>
            let A := EX.extract_v (fuelE - 1) b ρ vA in
            let ρ' := <[v := 0]> (EX.env_shift ρ) in
            let body :=
              match RO.b_fix_body b !! v with
              | Some vbody => EX.extract_v (fuelE - 1) b ρ' vbody
              | None => EX.extract_node (fuelE - 1) b ρ' v
              end
            in
            T.tFix A body
        | None => EX.extract_node (fuelE - 1) b ρ v
        end
    | Some k => T.tVar k
    end.
Proof.
  intros Hfuel.
  destruct fuelE as [|f1]; [lia|].
  destruct f1 as [|f2]; [lia|].
  cbn [EX.extract_v].
  reflexivity.
Qed.

Lemma extract_node_unfold_ge1
    (fuelE : nat) (b : RO.builder) (ρ : EX.fix_env) (v : nat) :
  fuelE >= 1 ->
  EX.extract_node fuelE b ρ v =
    match EX.lookup_node b v with
    | RO.nVar x => T.tVar x
    | RO.nSort i => T.tSort i
    | RO.nPi =>
        match EX.lookup_succ b v with
        | [vA; vB] =>
            let A := EX.extract_v (fuelE - 1) b ρ vA in
            let B := EX.extract_v (fuelE - 1) b (EX.env_shift ρ) vB in
            T.tPi A B
        | _ => T.tVar 0
        end
    | RO.nLam =>
        match EX.lookup_succ b v with
        | [vA; vt] =>
            let A := EX.extract_v (fuelE - 1) b ρ vA in
            let t := EX.extract_v (fuelE - 1) b (EX.env_shift ρ) vt in
            T.tLam A t
        | _ => T.tVar 0
        end
    | RO.nApp =>
        match EX.lookup_succ b v with
        | [vf; va] => T.tApp (EX.extract_v (fuelE - 1) b ρ vf) (EX.extract_v (fuelE - 1) b ρ va)
        | _ => T.tVar 0
        end
    | RO.nInd ind => T.tInd ind
    | RO.nRoll ind ctor nparams nrecs =>
        let xs := EX.lookup_succ b v in
        let ps := take nparams xs in
        let rs := drop nparams xs in
        T.tRoll ind ctor
          (EX.extract_list EX.extract_v fuelE b ρ ps)
          (EX.extract_list EX.extract_v fuelE b ρ rs)
    | RO.nCase ind nbrs =>
        match EX.lookup_succ b v with
        | vscrut :: vC :: brs =>
            T.tCase ind (EX.extract_v (fuelE - 1) b ρ vscrut) (EX.extract_v (fuelE - 1) b ρ vC)
              (EX.extract_list EX.extract_v fuelE b ρ (take nbrs brs))
        | _ => T.tVar 0
        end
    | RO.nSubstNil _ => T.tVar 0
    | RO.nSubstCons _ => T.tVar 0
    | RO.nBack =>
        match EX.lookup_succ b v with
        | [target; sv] =>
            match ρ !! target with
            | Some k => EX.apps (T.tVar k) (EX.subst_args (fuelE - 1) b ρ sv)
            | None => T.tVar 0
            end
        | _ => T.tVar 0
        end
    end.
Proof.
  intros Hfuel.
  destruct fuelE as [|f]; [lia|].
  cbn [EX.extract_node].
  replace (S f - 1) with f by lia.
  reflexivity.
Qed.

(** A standalone correctness lemma for the `tPi` case.

    This is the exact structure we’ll later plug into the mutual proof.
    It assumes IH-style correctness for the two recursive compilation calls.
*)
Lemma extract_compile_tm_tPi_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (A B : T.tm) (b : RO.builder)
    (IHA : forall (b0 : RO.builder),
        fuelC >= S (T.size A) ->
        dom_lt b0 ->
        closed_lt b0 (RO.b_next b0) ->
        nodup_targets ρ ->
        targets_lt ρ (RO.b_next b0) ->
        fuelE - 2 >= fuel_cost_tm A ->
        let '(vA, bA) := RO.compile_tm fuelC ρ A b0 in
        EX.extract_v (fuelE - 2) bA (fix_env_of ρ) vA = A)
    (IHB : forall (b1 : RO.builder),
        fuelC >= S (T.size B) ->
        dom_lt b1 ->
        closed_lt b1 (RO.b_next b1) ->
        nodup_targets (None :: ρ) ->
        targets_lt (None :: ρ) (RO.b_next b1) ->
        fuelE - 2 >= fuel_cost_tm B ->
        let '(vB, bB) := RO.compile_tm fuelC (None :: ρ) B b1 in
        EX.extract_v (fuelE - 2) bB (fix_env_of (None :: ρ)) vB = B) :
  S fuelC >= S (T.size (T.tPi A B)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tPi A B) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tPi A B) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tPi A B.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.
  cbn [RO.compile_tm].
  (* compile A *)
  destruct (RO.compile_tm fuelC ρ A b) as [vA b1] eqn:HA.
  assert (HfuelA : fuelC >= S (T.size A)) by (cbn [T.size] in HfuelC; lia).
  pose proof (compile_tm_dom_lt fuelC ρ A b Hdom) as Hdom1.
  rewrite HA in Hdom1.
  pose proof (compile_tm_closed fuelC ρ A b (conj Hdom Hcl) Htlt) as Hcl1.
  rewrite HA in Hcl1.
  pose proof (compile_tm_bnext_mono fuelC ρ A b) as Hmn1.
  rewrite HA in Hmn1.
  assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).

  (* compile B *)
  destruct (RO.compile_tm fuelC (None :: ρ) B b1) as [vB b2] eqn:HB.
  assert (HfuelB : fuelC >= S (T.size B)) by (cbn [T.size] in HfuelC; lia).
  assert (HnodupB : nodup_targets (None :: ρ)) by (simpl; exact Hnodup).
  assert (HtltB : targets_lt (None :: ρ) (RO.b_next b1)) by (simpl; exact Htlt1).
  pose proof (compile_tm_dom_lt fuelC (None :: ρ) B b1 Hdom1) as Hdom2.
  rewrite HB in Hdom2.
  pose proof (compile_tm_closed fuelC (None :: ρ) B b1 (conj Hdom1 Hcl1) HtltB) as Hcl2.
  rewrite HB in Hcl2.
  pose proof (compile_tm_bnext_mono fuelC (None :: ρ) B b1) as Hmn2.
  rewrite HB in Hmn2.

  (* fuel adequacy for children *)
  pose proof (fuel_cost_tPi_subterms A B fuelE HfuelE) as [HfuelEA HfuelEB].

  (* apply IHs *)
  pose proof (IHA b HfuelA Hdom Hcl Hnodup Htlt HfuelEA) as HexA.
  rewrite HA in HexA.
  pose proof (IHB b1 HfuelB Hdom1 Hcl1 HnodupB HtltB HfuelEB) as HexB.
  rewrite HB in HexB.

  (* build the Pi node *)
  unfold RO.fresh.
  simpl.
  set (v := RO.b_next b2).
  set (b3 :=
         {| RO.b_next := S v;
            RO.b_label := RO.b_label b2;
            RO.b_succ := RO.b_succ b2;
            RO.b_fix_ty := RO.b_fix_ty b2;
            RO.b_fix_body := RO.b_fix_body b2 |}).
  set (b4 := RO.put v RO.nPi [vA; vB] b3).

  (* show `v` is fresh w.r.t. fix-env-of ρ *)
  assert (Htlt2 : targets_lt ρ v).
  { unfold v.
    eapply targets_lt_mono; [exact Htlt|].
    eapply Nat.le_trans; [exact Hmn1|exact Hmn2]. }
  assert (Hρv : fix_env_of ρ !! v = None) by (apply fix_env_of_lookup_None_of_targets_lt; exact Htlt2).

  (* show no fix metadata at the Pi node (fresh vertex) *)
  assert (Hfx2 : RO.b_fix_ty b2 !! v = None).
  { destruct (RO.b_fix_ty b2 !! v) as [w|] eqn:Hfx; [|reflexivity].
    exfalso.
    destruct Hdom2 as [_ [_ Hf]].
    specialize (Hf v w Hfx).
    unfold v in Hf.
    exact (Nat.lt_irrefl _ Hf). }
  assert (Hfx : RO.b_fix_ty b4 !! v = None).
  { unfold b4, RO.put. simpl. exact Hfx2. }

  (* unfold extraction at the new root `v` *)
  assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 (T.tPi A B)); lia).
  rewrite (extract_v_unfold_ge2 fuelE b4 (fix_env_of ρ) v Hfuel_ge2).
  (* make the two matches deterministic *)
  replace (fix_env_of ρ !! v) with (@None nat) by (symmetry; exact Hρv).
  replace (RO.b_fix_ty b4 !! v) with (@None nat) by (symmetry; exact Hfx).
  cbn.

  (* unfold the Pi node itself *)
  assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
  rewrite (extract_node_unfold_ge1 (fuelE - 1) b4 (fix_env_of ρ) v Hfuel_ge1).
  assert (Hnode : EX.lookup_node b4 v = RO.nPi).
  { unfold b4.
    apply lookup_node_put_eq. }
  assert (Hsucc : EX.lookup_succ b4 v = [vA; vB]).
  { unfold b4.
    apply lookup_succ_put_eq. }
  rewrite Hnode.
  rewrite Hsucc.
  (* normalize child fuel *)
  replace (fuelE - 1 - 1) with (fuelE - 2) by lia.
  cbn.

  (* lift children extraction results across builder extensions *)
  assert (HvA_lt_b1 : vA < RO.b_next b1).
  { pose proof (compile_tm_root_lt fuelC ρ A b) as HvA.
    rewrite HA in HvA.
    exact HvA. }
  assert (HvB_lt_b2 : vB < RO.b_next b2).
  { pose proof (compile_tm_root_lt fuelC (None :: ρ) B b1) as HvB.
    rewrite HB in HvB.
    exact HvB. }

  (* b1 -> b2 extensionality (compiling B extends builder) *)
  pose proof (compile_tm_preserves_lt fuelC (None :: ρ) B b1) as Hpres12.
  rewrite HB in Hpres12.
  assert (Hagree12 : forall k,
            k < RO.b_next b1 ->
            b2.(RO.b_label) !! k = b1.(RO.b_label) !! k
            /\ b2.(RO.b_succ) !! k = b1.(RO.b_succ) !! k
            /\ b2.(RO.b_fix_ty) !! k = b1.(RO.b_fix_ty) !! k
            /\ b2.(RO.b_fix_body) !! k = b1.(RO.b_fix_body) !! k)
    by (intros k Hk; apply Hpres12; exact Hk).
  pose proof (extract_ext_inst b1 b2 (fix_env_of ρ) (RO.b_next b1) (fuelE - 2) Hagree12 Hcl1)
    as [Hexv12 [Hexn12 Hexs12]].

  (* b2 -> b4 extensionality (put at fresh v preserves old vertices) *)
  assert (Hagree24 : forall k,
            k < v ->
            b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
            /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
            /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k
            /\ b4.(RO.b_fix_body) !! k = b2.(RO.b_fix_body) !! k).
  { intros k Hk.
    unfold b4, RO.put. simpl.
    assert (k <> v) by lia.
    repeat split; try reflexivity; rewrite lookup_insert_ne; auto. }
  pose proof (extract_ext_inst b2 b4 (fix_env_of ρ) v (fuelE - 2) Hagree24 Hcl2)
    as [Hexv24 [Hexn24 Hexs24]].
  pose proof (extract_ext_inst b2 b4 (EX.env_shift (fix_env_of ρ)) v (fuelE - 2) Hagree24 Hcl2)
    as [Hexv24s [Hexn24s Hexs24s]].

  assert (HvA_lt_v : vA < v).
  { unfold v.
    eapply Nat.lt_le_trans; [exact HvA_lt_b1|exact Hmn2]. }
  assert (HvB_lt_v : vB < v) by (unfold v; exact HvB_lt_b2).

  (* rewrite env shift for B *)
  rewrite fix_env_of_cons_none in HexB.

  (* A child *)
  rewrite <- (Hexv24 vA HvA_lt_v).
  rewrite <- (Hexv12 vA HvA_lt_b1).
  rewrite HexA.

  (* B child (under shift) *)
  rewrite <- (Hexv24s vB HvB_lt_v).
  rewrite HexB.

  reflexivity.
Qed.

(** A standalone correctness lemma for the `tLam` case.

    This matches `extract_compile_tm_tPi_case`, but for lambdas.
*)
Lemma extract_compile_tm_tLam_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (A t0 : T.tm) (b : RO.builder)
    (IHA : forall (b0 : RO.builder),
        fuelC >= S (T.size A) ->
        dom_lt b0 ->
        closed_lt b0 (RO.b_next b0) ->
        nodup_targets ρ ->
        targets_lt ρ (RO.b_next b0) ->
        fuelE - 2 >= fuel_cost_tm A ->
        let '(vA, bA) := RO.compile_tm fuelC ρ A b0 in
        EX.extract_v (fuelE - 2) bA (fix_env_of ρ) vA = A)
    (IHt : forall (b1 : RO.builder),
        fuelC >= S (T.size t0) ->
        dom_lt b1 ->
        closed_lt b1 (RO.b_next b1) ->
        nodup_targets (None :: ρ) ->
        targets_lt (None :: ρ) (RO.b_next b1) ->
        fuelE - 2 >= fuel_cost_tm t0 ->
        let '(vt, bT) := RO.compile_tm fuelC (None :: ρ) t0 b1 in
        EX.extract_v (fuelE - 2) bT (fix_env_of (None :: ρ)) vt = t0) :
  S fuelC >= S (T.size (T.tLam A t0)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tLam A t0) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tLam A t0) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tLam A t0.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.
  cbn [RO.compile_tm].
  (* compile A *)
  destruct (RO.compile_tm fuelC ρ A b) as [vA b1] eqn:HA.
  assert (HfuelA : fuelC >= S (T.size A)) by (cbn [T.size] in HfuelC; lia).
  pose proof (compile_tm_dom_lt fuelC ρ A b Hdom) as Hdom1.
  rewrite HA in Hdom1.
  pose proof (compile_tm_closed fuelC ρ A b (conj Hdom Hcl) Htlt) as Hcl1.
  rewrite HA in Hcl1.
  pose proof (compile_tm_bnext_mono fuelC ρ A b) as Hmn1.
  rewrite HA in Hmn1.
  assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).

  (* compile body *)
  destruct (RO.compile_tm fuelC (None :: ρ) t0 b1) as [vt b2] eqn:HB.
  assert (Hfuelt : fuelC >= S (T.size t0)) by (cbn [T.size] in HfuelC; lia).
  assert (Hnodupt : nodup_targets (None :: ρ)) by (simpl; exact Hnodup).
  assert (HtltB : targets_lt (None :: ρ) (RO.b_next b1)) by (simpl; exact Htlt1).
  pose proof (compile_tm_dom_lt fuelC (None :: ρ) t0 b1 Hdom1) as Hdom2.
  rewrite HB in Hdom2.
  pose proof (compile_tm_closed fuelC (None :: ρ) t0 b1 (conj Hdom1 Hcl1) HtltB) as Hcl2.
  rewrite HB in Hcl2.
  pose proof (compile_tm_bnext_mono fuelC (None :: ρ) t0 b1) as Hmn2.
  rewrite HB in Hmn2.

  pose proof (fuel_cost_tLam_subterms A t0 fuelE HfuelE) as [HfuelEA HfuelEt].

  pose proof (IHA b HfuelA Hdom Hcl Hnodup Htlt HfuelEA) as HexA.
  rewrite HA in HexA.
  pose proof (IHt b1 Hfuelt Hdom1 Hcl1 Hnodupt HtltB HfuelEt) as Hext.
  rewrite HB in Hext.

  (* build the Lam node *)
  unfold RO.fresh.
  simpl.
  set (v := RO.b_next b2).
  set (b3 :=
         {| RO.b_next := S v;
            RO.b_label := RO.b_label b2;
            RO.b_succ := RO.b_succ b2;
            RO.b_fix_ty := RO.b_fix_ty b2;
            RO.b_fix_body := RO.b_fix_body b2 |}).
  set (b4 := RO.put v RO.nLam [vA; vt] b3).

  (* show `v` is fresh w.r.t. fix-env-of ρ *)
  assert (Htlt2 : targets_lt ρ v).
  { unfold v.
    eapply targets_lt_mono; [exact Htlt|].
    eapply Nat.le_trans; [exact Hmn1|exact Hmn2]. }
  assert (Hρv : fix_env_of ρ !! v = None) by (apply fix_env_of_lookup_None_of_targets_lt; exact Htlt2).

  (* show no fix metadata at the Lam node (fresh vertex) *)
  assert (Hfx2 : RO.b_fix_ty b2 !! v = None).
  { destruct (RO.b_fix_ty b2 !! v) as [w|] eqn:Hfx; [|reflexivity].
    exfalso.
    destruct Hdom2 as [_ [_ Hf]].
    specialize (Hf v w Hfx).
    unfold v in Hf.
    exact (Nat.lt_irrefl _ Hf). }
  assert (Hfx : RO.b_fix_ty b4 !! v = None).
  { unfold b4, RO.put. simpl. exact Hfx2. }

  assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 (T.tLam A t0)); lia).
  rewrite (extract_v_unfold_ge2 fuelE b4 (fix_env_of ρ) v Hfuel_ge2).
  replace (fix_env_of ρ !! v) with (@None nat) by (symmetry; exact Hρv).
  replace (RO.b_fix_ty b4 !! v) with (@None nat) by (symmetry; exact Hfx).
  cbn.

  assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
  rewrite (extract_node_unfold_ge1 (fuelE - 1) b4 (fix_env_of ρ) v Hfuel_ge1).
  assert (Hnode : EX.lookup_node b4 v = RO.nLam).
  { unfold b4. apply lookup_node_put_eq. }
  assert (Hsucc : EX.lookup_succ b4 v = [vA; vt]).
  { unfold b4. apply lookup_succ_put_eq. }
  rewrite Hnode.
  rewrite Hsucc.
  replace (fuelE - 1 - 1) with (fuelE - 2) by lia.
  cbn.

  (* lift children extraction results across builder extensions *)
  assert (HvA_lt_b1 : vA < RO.b_next b1).
  { pose proof (compile_tm_root_lt fuelC ρ A b) as HvA.
    rewrite HA in HvA.
    exact HvA. }
  assert (Hvt_lt_b2 : vt < RO.b_next b2).
  { pose proof (compile_tm_root_lt fuelC (None :: ρ) t0 b1) as Hvt.
    rewrite HB in Hvt.
    exact Hvt. }

  pose proof (compile_tm_preserves_lt fuelC (None :: ρ) t0 b1) as Hpres12.
  rewrite HB in Hpres12.
  assert (Hagree12 : forall k,
            k < RO.b_next b1 ->
            b2.(RO.b_label) !! k = b1.(RO.b_label) !! k
            /\ b2.(RO.b_succ) !! k = b1.(RO.b_succ) !! k
            /\ b2.(RO.b_fix_ty) !! k = b1.(RO.b_fix_ty) !! k
            /\ b2.(RO.b_fix_body) !! k = b1.(RO.b_fix_body) !! k)
    by (intros k Hk; apply Hpres12; exact Hk).
  pose proof (extract_ext_inst b1 b2 (fix_env_of ρ) (RO.b_next b1) (fuelE - 2) Hagree12 Hcl1)
    as [Hexv12 [Hexn12 Hexs12]].

  assert (Hagree24 : forall k,
            k < v ->
            b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
            /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
            /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k
            /\ b4.(RO.b_fix_body) !! k = b2.(RO.b_fix_body) !! k).
  { intros k Hk.
    unfold b4, RO.put. simpl.
    assert (k <> v) by lia.
    repeat split; try reflexivity; rewrite lookup_insert_ne; auto. }
  pose proof (extract_ext_inst b2 b4 (fix_env_of ρ) v (fuelE - 2) Hagree24 Hcl2)
    as [Hexv24 [Hexn24 Hexs24]].
  pose proof (extract_ext_inst b2 b4 (EX.env_shift (fix_env_of ρ)) v (fuelE - 2) Hagree24 Hcl2)
    as [Hexv24s [Hexn24s Hexs24s]].

  assert (HvA_lt_v : vA < v).
  { unfold v.
    eapply Nat.lt_le_trans; [exact HvA_lt_b1|exact Hmn2]. }
  assert (Hvt_lt_v : vt < v) by (unfold v; exact Hvt_lt_b2).

  rewrite fix_env_of_cons_none in Hext.

  rewrite <- (Hexv24 vA HvA_lt_v).
  rewrite <- (Hexv12 vA HvA_lt_b1).
  rewrite HexA.

  rewrite <- (Hexv24s vt Hvt_lt_v).
  rewrite Hext.

  reflexivity.
Qed.

Lemma apps_tm_eq_apps (t : T.tm) (us : list T.tm) :
  apps_tm t us = EX.apps t us.
Proof.
  revert t.
  induction us as [|u us IH]; intros t; cbn [apps_tm EX.apps].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** A standalone correctness lemma for the `tApp` case.

    This covers both the ordinary `nApp` compilation path and the backlink `nBack`
    path (with explicit substitution evidence).

    It assumes IH-style correctness for the two direct subterms (`t1`, `u1`) and
    a list-level correctness hypothesis for extracting compiled argument lists.
*)
Lemma extract_compile_tm_tApp_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (t1 u1 : T.tm) (b : RO.builder)
    (IHt1 : forall (b0 : RO.builder),
        fuelC >= S (T.size t1) ->
        dom_lt b0 ->
        closed_lt b0 (RO.b_next b0) ->
        nodup_targets ρ ->
        targets_lt ρ (RO.b_next b0) ->
        fuelE - 2 >= fuel_cost_tm t1 ->
        let '(v1, b1) := RO.compile_tm fuelC ρ t1 b0 in
        EX.extract_v (fuelE - 2) b1 (fix_env_of ρ) v1 = t1)
    (IHu1 : forall (b1 : RO.builder),
        fuelC >= S (T.size u1) ->
        dom_lt b1 ->
        closed_lt b1 (RO.b_next b1) ->
        nodup_targets ρ ->
        targets_lt ρ (RO.b_next b1) ->
        fuelE - 2 >= fuel_cost_tm u1 ->
        let '(v2, b2) := RO.compile_tm fuelC ρ u1 b1 in
        EX.extract_v (fuelE - 2) b2 (fix_env_of ρ) v2 = u1)
    (IHlist : forall (ts : list T.tm) (b0 : RO.builder),
        fuelC >= list_size ts ->
        dom_lt b0 ->
        closed_lt b0 (RO.b_next b0) ->
        nodup_targets ρ ->
        targets_lt ρ (RO.b_next b0) ->
        fuelE - 2 >= fuel_cost_list ts ->
        let '(vs, b') := RO.compile_list fuelC ρ ts b0 in
        EX.extract_list EX.extract_v (fuelE - 2) b' (fix_env_of ρ) vs = ts) :
  S fuelC >= S (T.size (T.tApp t1 u1)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tApp t1 u1) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tApp t1 u1) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tApp t1 u1.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.
  set (t := T.tApp t1 u1).
  destruct (RO.app_view t) as [h args] eqn:Hview.
  cbn [RO.compile_tm].
  rewrite Hview.
  destruct h as
      [x
      |i
      |A B
      |A0 t0
      |t10 t20
      |A0 body0
      |I
      |I c params recs
      |I scrut C brs].
  - (* h = tVar x: possible backlink *)
    destruct (nth_error ρ x) as [[target|]|] eqn:Hnth.
    + (* backlink case *)
      (* compilation path *)
      destruct (RO.compile_list fuelC ρ args b) as [v_args b1] eqn:Hargs.
      destruct (RO.fresh b1) as [sv_nil b2] eqn:Hfr_nil.
      set (b3 := RO.put sv_nil (RO.nSubstNil 0) [] b2).
      destruct (RO.build_subst_chain v_args sv_nil b3) as [sv b4] eqn:Hch.
      destruct (RO.fresh b4) as [v_back b5] eqn:Hfr_back.
      set (b6 := RO.put v_back RO.nBack [target; sv] b5).

      (* relate t to its spine *)
      assert (Ht_apps : t = apps_tm (T.tVar x) args).
      { pose proof (app_view_correct t) as Happ.
        rewrite Hview in Happ.
        exact Happ. }

      (* fuel facts *)
      assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 t); lia).
      assert (HfuelE2 : fuelE - 2 >= fuel_cost_list args).
      { (* fuel_cost_tm (apps_tm (tVar x) args) dominates list cost of args *)
        rewrite Ht_apps in HfuelE.
        pose proof (fuel_cost_apps_tm_ge (T.tVar x) args) as Hge.
        cbn [fuel_cost_tm] in Hge.
        lia. }

      (* list correctness for compiled args *)
      assert (HfuelC_args : fuelC >= list_size args).
      { (* crude but sufficient: list_size args <= T.size (apps_tm (tVar x) args) *)
        rewrite Ht_apps in HfuelC.
        cbn [T.size] in HfuelC.
        (* `list_size` is at most `size` for spines headed by a variable. *)
        unfold list_size, list_max_size.
        destruct args as [|u us]; [cbn in *; lia|].
        simpl.
        lia. }
      pose proof (IHlist args b HfuelC_args Hdom Hcl Hnodup Htlt HfuelE2) as Hext_args.
      rewrite Hargs in Hext_args.

      (* show root is fresh w.r.t. fix-env-of ρ *)
      pose proof (fresh_fst_eq b4) as Hv_back_eq.
      rewrite Hfr_back in Hv_back_eq. simpl in Hv_back_eq.
      subst v_back.
      assert (Hb_le_b4 : RO.b_next b <= RO.b_next b4).
      { pose proof (compile_list_bnext_mono fuelC ρ args b) as Hb01.
        rewrite Hargs in Hb01. simpl in Hb01.
        pose proof (fresh_snd_next b1) as Hb2.
        rewrite Hfr_nil in Hb2. simpl in Hb2.
        pose proof (build_subst_chain_bnext_mono v_args (RO.b_next b1) b3) as Hb34.
        (* `sv_nil = b_next b1` *)
        pose proof (fresh_fst_eq b1) as Hsv_nil.
        rewrite Hfr_nil in Hsv_nil. simpl in Hsv_nil.
        subst sv_nil.
        rewrite Hch in Hb34. simpl in Hb34.
        lia. }
      assert (Htlt_back : targets_lt ρ (RO.b_next b4)).
      { eapply targets_lt_mono; [exact Htlt|exact Hb_le_b4]. }
      assert (Hρv : fix_env_of ρ !! (RO.b_next b4) = None)
        by (apply fix_env_of_lookup_None_of_targets_lt; exact Htlt_back).

      (* show `b_fix_ty` is empty at the backlink node *)
      assert (Hfx : RO.b_fix_ty b6 !! (RO.b_next b4) = None).
      { (* `b_fix_ty` is unchanged from `b` and `RO.b_next b4 >= RO.b_next b` *)
        destruct (RO.b_fix_ty b6 !! (RO.b_next b4)) as [w|] eqn:Hlk; [|reflexivity].
        exfalso.
        destruct Hdom as [_ [_ Hf]].
        (* b_fix_ty unchanged by fresh/put/build_subst_chain *)
        (* we only need the domain property: keys must be < b_next b, contradiction *)
        specialize (Hf (RO.b_next b4) w).
        assert (RO.b_fix_ty b !! RO.b_next b4 = Some w).
        { (* b_fix_ty never changes along this path *)
          (* unfold the builder chain to see fix_ty field is preserved *)
          unfold b6, RO.put in Hlk.
          simpl in Hlk.
          exact Hlk.
        }
        specialize (Hf H).
        lia. }

      (* unfold extraction at root *)
      rewrite (extract_v_unfold_ge2 fuelE b6 (fix_env_of ρ) (RO.b_next b4) Hfuel_ge2).
      replace (fix_env_of ρ !! RO.b_next b4) with (@None nat) by (symmetry; exact Hρv).
      replace (RO.b_fix_ty b6 !! RO.b_next b4) with (@None nat) by (symmetry; exact Hfx).
      cbn.

      (* unfold the backlink node *)
      assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
      rewrite (extract_node_unfold_ge1 (fuelE - 1) b6 (fix_env_of ρ) (RO.b_next b4) Hfuel_ge1).
      assert (Hnode : EX.lookup_node b6 (RO.b_next b4) = RO.nBack).
      { unfold b6.
        apply lookup_node_put_eq. }
      assert (Hsucc : EX.lookup_succ b6 (RO.b_next b4) = [target; sv]).
      { unfold b6.
        apply lookup_succ_put_eq. }
      rewrite Hnode.
      rewrite Hsucc.
      cbn.

      (* environment lookup for the backlink target *)
      assert (Htarget : fix_env_of ρ !! target = Some x).
      { eapply fix_env_of_nth_some; [exact Hnodup|].
        exact Hnth. }
      rewrite Htarget.

      (* normalize child fuel *)
      replace (fuelE - 1 - 1) with (fuelE - 2) by lia.

      (* subst_args correctness via the subst-chain lemma *)
      assert (Hsv_nil_eq : sv_nil = RO.b_next b1).
      { pose proof (fresh_fst_eq b1) as Hsv.
        rewrite Hfr_nil in Hsv. simpl in Hsv.
        exact Hsv. }
      subst sv_nil.

      (* properties needed by subst_args_build_subst_chain on b3 *)
      assert (Hdom3 : dom_lt b3).
      { subst b3.
        apply dom_lt_put.
        - (* dom_lt for b2 *)
          pose proof (compile_list_dom_lt fuelC ρ args b Hdom) as Hdom1.
          rewrite Hargs in Hdom1.
          pose proof (dom_lt_fresh b1 Hdom1) as Hdom2.
          rewrite Hfr_nil in Hdom2. simpl in Hdom2.
          exact Hdom2.
        - (* sv_nil < b_next b2 *)
          pose proof (fresh_snd_next b1) as Hb2.
          rewrite Hfr_nil in Hb2. simpl in Hb2.
          lia. }
      assert (Hcl3 : closed_lt b3 (RO.b_next b3)).
      { subst b3.
        (* b2 is closed, and put at fresh vertex preserves closedness *)
        pose proof (compile_list_closed fuelC ρ args b (conj Hdom Hcl) Htlt) as Hcl1.
        rewrite Hargs in Hcl1.
        pose proof (fresh_snd_next b1) as Hb2.
        rewrite Hfr_nil in Hb2. simpl in Hb2.
        (* closedness for b2 *)
        pose proof (closed_lt_fresh b1 Hdom1 Hcl1) as Hcl2.
        rewrite Hfr_nil in Hcl2.
        simpl in Hcl2.
        apply (closed_lt_put_over b2 (RO.b_next b2) (RO.b_next b1) (RO.nSubstNil 0) [] Hcl2).
        - lia.
        - constructor. }
      assert (Hsv_lt : RO.b_next b1 < RO.b_next b3).
      { subst b3.
        pose proof (fresh_snd_next b1) as Hb2.
        rewrite Hfr_nil in Hb2. simpl in Hb2.
        simpl.
        lia. }
      assert (Hlbl_nil : b3.(RO.b_label) !! RO.b_next b1 = Some (RO.nSubstNil 0)).
      { subst b3.
        unfold RO.put.
        simpl.
        rewrite lookup_insert.
        reflexivity. }
      assert (Hsucc_nil : b3.(RO.b_succ) !! RO.b_next b1 = Some []).
      { subst b3.
        unfold RO.put.
        simpl.
        rewrite lookup_insert.
        reflexivity. }
      assert (Hargs_lt : Forall (fun u => u < RO.b_next b3) v_args).
      { (* roots are < b_next b1, and b_next b1 < b_next b3 *)
        pose proof (compile_list_roots_lt fuelC ρ args b) as Hroots.
        rewrite Hargs in Hroots.
        eapply Forall_lt_mono; [exact Hroots|].
        lia. }

      pose proof (subst_args_build_subst_chain (fuelE - 2) (fix_env_of ρ) v_args (RO.b_next b1) b3
                    Hdom3 Hcl3 ltac:(lia) Hlbl_nil Hsucc_nil Hargs_lt)
        as Hsubst.
      rewrite Hch in Hsubst.

      (* lift subst_args and extract_list from b4 to b6 (put at fresh vertex) *)
      assert (Hpres46 : preserves_lt b4 b6).
      { (* b6 = put at v_back = b_next b4 *)
        subst b6.
        apply preserves_lt_put.
        lia. }
      pose proof (@extract_ext b4 b6 (RO.b_next b4) Hpres46 Hcl2 (fuelE - 2)) as [Hexv46 [Hexn46 [Hexs46 Hexl46]]].

      assert (Hsv_lt_vback : sv < RO.b_next b4).
      { pose proof (build_subst_chain_root_lt v_args (RO.b_next b1) b3 ltac:(lia)) as Hsvlt.
        rewrite Hch in Hsvlt.
        simpl in Hsvlt.
        exact Hsvlt. }

      rewrite <- (Hexs46 (fix_env_of ρ) sv Hsv_lt_vback).
      rewrite Hsubst.

      (* convert extract_vs to extract_list *)
      rewrite (extract_vs_eq_extract_list (fuelE - 2) b4 (fix_env_of ρ) v_args).

      (* lift compiled-args extraction from b1 to b4 and then to b6 *)
      assert (Hpres14 : preserves_lt b1 b4).
      { (* b4 is built from b1 by fresh+put+build_subst_chain *)
        pose proof (preserves_lt_fresh b1) as Hpres12.
        pose proof (preserves_lt_put_over b1 (snd (RO.fresh b1)) (RO.b_next b1) (RO.nSubstNil 0) [] Hpres12 ltac:(lia)) as Hpres13.
        (* build_subst_chain preserves b1 *)
        eapply preserves_lt_build_subst_chain_over.
        - exact Hpres13.
        - lia. }
      pose proof (@extract_ext b1 b4 (RO.b_next b1) Hpres14 Hcl1 (fuelE - 2)) as [_ [_ [_ Hexl14]]].

      pose proof (compile_list_roots_lt fuelC ρ args b) as Hroots.
      rewrite Hargs in Hroots.

      rewrite <- (Hexl46 (fix_env_of ρ) v_args).
      2: { eapply Forall_lt_mono; [exact Hroots|]. lia. }
      rewrite <- (Hexl14 (fix_env_of ρ) v_args).
      2: { eapply Forall_lt_mono; [exact Hroots|].
           pose proof (fresh_snd_next b1) as Hb2.
           rewrite Hfr_nil in Hb2. simpl in Hb2.
           pose proof (build_subst_chain_bnext_mono v_args (RO.b_next b1) b3) as Hb34.
           rewrite Hch in Hb34. simpl in Hb34.
           lia. }

      rewrite Hext_args.

      (* close: apps term equals original app spine *)
      rewrite <- apps_tm_eq_apps.
      rewrite <- Ht_apps.
      reflexivity.

    + (* h = tVar x, but not a backlink: ordinary app *)
      (* ordinary compilation path *)
      destruct (RO.compile_tm fuelC ρ t1 b) as [v1 b1] eqn:H1.
      destruct (RO.compile_tm fuelC ρ u1 b1) as [v2 b2] eqn:H2.
      destruct (RO.fresh b2) as [v b3] eqn:Hfr.
      set (b4 := RO.put v RO.nApp [v1; v2] b3).

      pose proof (fuel_cost_tApp_subterms t1 u1 fuelE HfuelE) as [HfuelEt1 HfuelEu1].
      assert (Hfuel1 : fuelC >= S (T.size t1)) by (cbn [T.size] in HfuelC; lia).
      assert (Hfuel2 : fuelC >= S (T.size u1)) by (cbn [T.size] in HfuelC; lia).

      pose proof (IHt1 b Hfuel1 Hdom Hcl Hnodup Htlt HfuelEt1) as Hex1.
      rewrite H1 in Hex1.

      pose proof (compile_tm_dom_lt fuelC ρ t1 b Hdom) as Hdom1.
      rewrite H1 in Hdom1.
      pose proof (compile_tm_closed fuelC ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1.
      rewrite H1 in Hcl1.
      pose proof (compile_tm_bnext_mono fuelC ρ t1 b) as Hb01.
      rewrite H1 in Hb01.
      assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hb01]).

      pose proof (IHu1 b1 Hfuel2 Hdom1 Hcl1 Hnodup Htlt1 HfuelEu1) as Hex2.
      rewrite H2 in Hex2.

      (* show v is fresh w.r.t env and fix_ty *)
      pose proof (fresh_fst_eq b2) as Hv.
      rewrite Hfr in Hv. simpl in Hv.
      subst v.
      assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt|]; exact (compile_tm_bnext_mono fuelC ρ t1 b)).
      assert (Hρv : fix_env_of ρ !! (RO.b_next b2) = None) by (apply fix_env_of_lookup_None_of_targets_lt; exact Htlt2).

      assert (Hfx2 : RO.b_fix_ty b2 !! RO.b_next b2 = None).
      { destruct (RO.b_fix_ty b2 !! RO.b_next b2) as [w|] eqn:Hfx; [|reflexivity].
        exfalso.
        destruct (compile_tm_dom_lt fuelC ρ u1 b1 Hdom1) as [_ [_ Hf]].
        rewrite H2 in Hf.
        specialize (Hf (RO.b_next b2) w Hfx).
        exact (Nat.lt_irrefl _ Hf). }
      assert (Hfx : RO.b_fix_ty b4 !! RO.b_next b2 = None).
      { unfold b4, RO.put. simpl. exact Hfx2. }

      assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 t); lia).
      rewrite (extract_v_unfold_ge2 fuelE b4 (fix_env_of ρ) (RO.b_next b2) Hfuel_ge2).
      replace (fix_env_of ρ !! RO.b_next b2) with (@None nat) by (symmetry; exact Hρv).
      replace (RO.b_fix_ty b4 !! RO.b_next b2) with (@None nat) by (symmetry; exact Hfx).
      cbn.

      assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
      rewrite (extract_node_unfold_ge1 (fuelE - 1) b4 (fix_env_of ρ) (RO.b_next b2) Hfuel_ge1).
      assert (Hnode : EX.lookup_node b4 (RO.b_next b2) = RO.nApp).
      { unfold b4. apply lookup_node_put_eq. }
      assert (Hsucc : EX.lookup_succ b4 (RO.b_next b2) = [v1; v2]).
      { unfold b4. apply lookup_succ_put_eq. }
      rewrite Hnode, Hsucc.
      replace (fuelE - 1 - 1) with (fuelE - 2) by lia.
      cbn.

      (* lift children extraction from intermediate builders *)
      assert (Hv1_lt : v1 < RO.b_next b1).
      { pose proof (compile_tm_root_lt fuelC ρ t1 b) as Hv1.
        rewrite H1 in Hv1.
        exact Hv1. }
      assert (Hv2_lt : v2 < RO.b_next b2).
      { pose proof (compile_tm_root_lt fuelC ρ u1 b1) as Hv2.
        rewrite H2 in Hv2.
        exact Hv2. }

      pose proof (compile_tm_preserves_lt fuelC ρ u1 b1) as Hpres12.
      rewrite H2 in Hpres12.
      pose proof (@extract_ext_inst b1 b2 (fix_env_of ρ) (RO.b_next b1) (fuelE - 2) Hpres12 Hcl1)
        as [Hexv12 [_ _]].

      assert (Hagree24 : forall k,
                k < RO.b_next b2 ->
                b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k
                /\ b4.(RO.b_fix_body) !! k = b2.(RO.b_fix_body) !! k).
      { intros k Hk.
        unfold b4, RO.put. simpl.
        assert (k <> RO.b_next b2) by lia.
        repeat split; try reflexivity; rewrite lookup_insert_ne; auto. }
      pose proof (extract_ext_inst b2 b4 (fix_env_of ρ) (RO.b_next b2) (fuelE - 2) Hagree24 (conj (proj1 (compile_tm_closed fuelC ρ u1 b1 (conj Hdom1 Hcl1) Htlt1)) (proj2 (compile_tm_closed fuelC ρ u1 b1 (conj Hdom1 Hcl1) Htlt1)))) as [Hexv24 _].

      rewrite <- (Hexv24 v1 ltac:(lia)).
      rewrite <- (Hexv12 v1 Hv1_lt).
      rewrite Hex1.

      rewrite <- (Hexv24 v2 ltac:(lia)).
      rewrite Hex2.

      reflexivity.
  - (* non-variable head: ordinary app *)
    (* we are in the ordinary app compilation branch *)
    destruct (RO.compile_tm fuelC ρ t1 b) as [v1 b1] eqn:H1.
    destruct (RO.compile_tm fuelC ρ u1 b1) as [v2 b2] eqn:H2.
    destruct (RO.fresh b2) as [v b3] eqn:Hfr.
    set (b4 := RO.put v RO.nApp [v1; v2] b3).

    pose proof (fuel_cost_tApp_subterms t1 u1 fuelE HfuelE) as [HfuelEt1 HfuelEu1].
    assert (Hfuel1 : fuelC >= S (T.size t1)) by (cbn [T.size] in HfuelC; lia).
    assert (Hfuel2 : fuelC >= S (T.size u1)) by (cbn [T.size] in HfuelC; lia).

    pose proof (IHt1 b Hfuel1 Hdom Hcl Hnodup Htlt HfuelEt1) as Hex1.
    rewrite H1 in Hex1.

    pose proof (compile_tm_dom_lt fuelC ρ t1 b Hdom) as Hdom1.
    rewrite H1 in Hdom1.
    pose proof (compile_tm_closed fuelC ρ t1 b (conj Hdom Hcl) Htlt) as Hcl1.
    rewrite H1 in Hcl1.
    pose proof (compile_tm_bnext_mono fuelC ρ t1 b) as Hb01.
    rewrite H1 in Hb01.
    assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hb01]).

    pose proof (IHu1 b1 Hfuel2 Hdom1 Hcl1 Hnodup Htlt1 HfuelEu1) as Hex2.
    rewrite H2 in Hex2.

    (* show v is fresh w.r.t env and fix_ty *)
    pose proof (fresh_fst_eq b2) as Hv.
    rewrite Hfr in Hv. simpl in Hv.
    subst v.
    assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt|]; exact Hb01).
    assert (Hρv : fix_env_of ρ !! (RO.b_next b2) = None) by (apply fix_env_of_lookup_None_of_targets_lt; exact Htlt2).

    assert (Hfx2 : RO.b_fix_ty b2 !! RO.b_next b2 = None).
    { destruct (RO.b_fix_ty b2 !! RO.b_next b2) as [w|] eqn:Hfx; [|reflexivity].
      exfalso.
      destruct (compile_tm_dom_lt fuelC ρ u1 b1 Hdom1) as [_ [_ Hf]].
      rewrite H2 in Hf.
      specialize (Hf (RO.b_next b2) w Hfx).
      exact (Nat.lt_irrefl _ Hf). }
    assert (Hfx : RO.b_fix_ty b4 !! RO.b_next b2 = None).
    { unfold b4, RO.put. simpl. exact Hfx2. }

    assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 t); lia).
    rewrite (extract_v_unfold_ge2 fuelE b4 (fix_env_of ρ) (RO.b_next b2) Hfuel_ge2).
    replace (fix_env_of ρ !! RO.b_next b2) with (@None nat) by (symmetry; exact Hρv).
    replace (RO.b_fix_ty b4 !! RO.b_next b2) with (@None nat) by (symmetry; exact Hfx).
    cbn.

    assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
    rewrite (extract_node_unfold_ge1 (fuelE - 1) b4 (fix_env_of ρ) (RO.b_next b2) Hfuel_ge1).
    assert (Hnode : EX.lookup_node b4 (RO.b_next b2) = RO.nApp).
    { unfold b4. apply lookup_node_put_eq. }
    assert (Hsucc : EX.lookup_succ b4 (RO.b_next b2) = [v1; v2]).
    { unfold b4. apply lookup_succ_put_eq. }
    rewrite Hnode, Hsucc.
    replace (fuelE - 1 - 1) with (fuelE - 2) by lia.
    cbn.

    (* lift children extraction from intermediate builders *)
    assert (Hv1_lt : v1 < RO.b_next b1).
    { pose proof (compile_tm_root_lt fuelC ρ t1 b) as Hv1.
      rewrite H1 in Hv1.
      exact Hv1. }

    pose proof (compile_tm_preserves_lt fuelC ρ u1 b1) as Hpres12.
    rewrite H2 in Hpres12.
    pose proof (extract_ext_inst b1 b2 (fix_env_of ρ) (RO.b_next b1) (fuelE - 2) Hpres12 Hcl1)
      as [Hexv12 _].

    assert (Hagree24 : forall k,
              k < RO.b_next b2 ->
              b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
              /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
              /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k
              /\ b4.(RO.b_fix_body) !! k = b2.(RO.b_fix_body) !! k).
    { intros k Hk.
      unfold b4, RO.put. simpl.
      assert (k <> RO.b_next b2) by lia.
      repeat split; try reflexivity; rewrite lookup_insert_ne; auto. }
    pose proof (extract_ext_inst b2 b4 (fix_env_of ρ) (RO.b_next b2) (fuelE - 2) Hagree24 Hcl2)
      as [Hexv24 _].

    rewrite <- (Hexv24 v1 ltac:(lia)).
    rewrite <- (Hexv12 v1 Hv1_lt).
    rewrite Hex1.

    rewrite <- (Hexv24 v2 ltac:(lia)).
    rewrite Hex2.

    reflexivity.
Qed.

(** A standalone correctness lemma for the `tFix` case.

    This is the hardest case: compilation ties a cycle by allocating a fresh target
    vertex `v` and then overwriting it with a copy of the compiled body root.
*)
Lemma extract_compile_tm_tFix_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (A body : T.tm) (b : RO.builder)
    (IHA : forall (b0 : RO.builder),
        fuelC >= S (T.size A) ->
        dom_lt b0 ->
        closed_lt b0 (RO.b_next b0) ->
        nodup_targets ρ ->
        targets_lt ρ (RO.b_next b0) ->
        fuelE - 1 >= fuel_cost_tm A ->
        let '(vA, b1) := RO.compile_tm fuelC ρ A b0 in
        EX.extract_v (fuelE - 1) b1 (fix_env_of ρ) vA = A)
    (IHbody : forall (b1' : RO.builder),
        fuelC >= S (T.size body) ->
        dom_lt b1' ->
        closed_lt b1' (RO.b_next b1') ->
        nodup_targets (Some (RO.b_next b) :: ρ) ->
        targets_lt (Some (RO.b_next b) :: ρ) (RO.b_next b1') ->
        fuelE >= fuel_cost_tm body ->
        let '(vbody, b2) := RO.compile_tm fuelC (Some (RO.b_next b) :: ρ) body b1' in
        EX.extract_v fuelE b2 (fix_env_of (Some (RO.b_next b) :: ρ)) vbody = body) :
  S fuelC >= S (T.size (T.tFix A body)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tFix A body) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tFix A body) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tFix A body.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.
  
  (* Unfold compilation of tFix *)
  cbn [RO.compile_tm].
  destruct (RO.fresh b) as [v b0] eqn:Hfr.
  destruct (RO.compile_tm fuelC ρ A b0) as [vA b1] eqn:HA.
  set (b1' := RO.put_fix_ty v vA b1).
  destruct (RO.compile_tm fuelC (Some v :: ρ) body b1') as [vbody b2] eqn:Hbody.
  set (b2' := RO.put_fix_body v vbody b2).
  
  (* Establish builder invariants through the pipeline *)
  assert (Hv_eq : v = RO.b_next b).
  { unfold RO.fresh in Hfr. injection Hfr as <- _. reflexivity. }
  
  assert (Hdom0 : dom_lt b0).
  { rewrite Hfr. apply dom_lt_fresh. exact Hdom. }
  
  assert (Hcl0 : closed_lt b0 (RO.b_next b0)).
  { rewrite Hfr. apply closed_lt_fresh. exact Hcl. }
  
  assert (Hwf0 : wf_builder b0) by (split; [exact Hdom0|exact Hcl0]).
  
  assert (Hdom1 : dom_lt b1).
  { rewrite <- HA. apply compile_tm_dom_lt. exact Hdom0. }
  
  assert (Hwf1 : wf_builder b1).
  { split.
    - exact Hdom1.
    - rewrite <- HA. apply compile_tm_closed. exact Hwf0. exact Htlt. }
  
  assert (Hcl1 : closed_lt b1 (RO.b_next b1)) by (destruct Hwf1; assumption).
  
  (* Monotonicity facts *)
  assert (Hmono_b0 : RO.b_next b <= RO.b_next b0).
  { rewrite Hfr. apply fresh_snd_next. }
  
  assert (Hmono_01 : RO.b_next b0 <= RO.b_next b1).
  { pose proof (compile_tm_bnext_mono fuelC ρ A b0) as Hm.
    rewrite HA in Hm. exact Hm. }
  
  assert (Hmono_b1 : RO.b_next b <= RO.b_next b1) by lia.
  
  (* b1' facts *)
  assert (Hdom1' : dom_lt b1').
  { unfold b1'. apply dom_lt_put_fix_ty.
    - exact Hdom1.
    - rewrite Hv_eq. lia. }
  
  assert (Hcl1' : closed_lt b1' (RO.b_next b1')).
  { unfold b1'. simpl.
    apply closed_lt_put_fix_ty_over.
    - exact Hcl1.
    - pose proof (compile_tm_root_lt fuelC ρ A b0) as HvA_lt.
      rewrite HA in HvA_lt. exact HvA_lt. }
  
  assert (Hwf1' : wf_builder b1') by (split; [exact Hdom1'|exact Hcl1']).
  
  (* targets_lt for (Some v :: ρ) *)
  assert (Htlt_body : targets_lt (Some v :: ρ) (RO.b_next b1')).
  { apply targets_lt_cons_fresh.
    - rewrite Hv_eq. unfold b1'. simpl. lia.
    - unfold b1'. simpl. eapply targets_lt_mono; [exact Htlt|lia]. }
  
  assert (Hnodup_body : nodup_targets (Some v :: ρ)).
  { apply nodup_targets_cons_fresh.
    - exact Hnodup.
    - rewrite Hv_eq. exact Htlt. }
  
  (* b2 facts *)
  assert (Hdom2 : dom_lt b2).
  { rewrite <- Hbody. apply compile_tm_dom_lt. exact Hdom1'. }
  
  assert (Hwf2 : wf_builder b2).
  { split.
    - exact Hdom2.
    - rewrite <- Hbody. apply compile_tm_closed. exact Hwf1'. exact Htlt_body. }
  
  assert (Hcl2 : closed_lt b2 (RO.b_next b2)) by (destruct Hwf2; assumption).
  
  assert (Hmono_12 : RO.b_next b1' <= RO.b_next b2).
  { pose proof (compile_tm_bnext_mono fuelC (Some v :: ρ) body b1') as Hm.
    rewrite Hbody in Hm. unfold b1' in Hm. simpl in Hm. exact Hm. }
  
  assert (Hmono_b2 : RO.b_next b <= RO.b_next b2).
  { unfold b1' in Hmono_12. simpl in Hmono_12. lia. }
  
  (* b2' facts *)
  assert (Hdom2' : dom_lt b2').
  { unfold b2'. apply dom_lt_put_fix_body.
    - exact Hdom2.
    - rewrite Hv_eq. lia. }
  
  assert (Hcl2' : closed_lt b2' (RO.b_next b2')).
  { unfold b2'. simpl.
    apply closed_lt_put_fix_body_over.
    - exact Hcl2.
    - pose proof (compile_tm_root_lt fuelC (Some v :: ρ) body b1') as Hvbody_lt.
      rewrite Hbody in Hvbody_lt. exact Hvbody_lt. }
  
  (* Unfold extraction of the compiled result *)
  apply extract_v_unfold_ge2.
  { cbn [fuel_cost_tm] in HfuelE. lia. }
  
  cbn [EX.extract_v].
  
  (* The fix_env should not have v bound (since v is fresh) *)
  assert (Hv_not_in_rho : fix_env_of ρ !! v = None).
  { rewrite Hv_eq.
    apply fix_env_of_lookup_None_of_targets_lt. exact Htlt. }
  
  rewrite Hv_not_in_rho.
  
  (* Show that b_fix_ty is set *)
  assert (Hfix_ty : RO.b_fix_ty b2' !! v = Some vA).
  { unfold b2', RO.put_fix_body. simpl.
    unfold b1', RO.put_fix_ty. simpl.
    rewrite lookup_insert_ne.
    - rewrite lookup_insert.
      rewrite decide_True by reflexivity.
      reflexivity.
    - intro Heq. 
      assert (v < RO.b_next b1).
      { rewrite <- Heq. rewrite <- HA.
        apply compile_tm_root_lt. }
      rewrite Hv_eq in H. lia. }
  
  rewrite Hfix_ty.
  
  (* Show that b_fix_body is set *)
  assert (Hfix_body : RO.b_fix_body b2' !! v = Some vbody).
  { unfold b2', RO.put_fix_body. simpl.
    rewrite lookup_insert.
    rewrite decide_True by reflexivity.
    reflexivity. }
  
  rewrite Hfix_body.
  
  (* Now we need to apply IH for A and body *)
  f_equal.
  
  - (* Type A *)
    (* We need to show: EX.extract_v (fuelE - 2) b2' (fix_env_of ρ) vA = A *)
    
    assert (HfuelC_A : fuelC >= S (T.size A)).
    { cbn [T.size] in HfuelC. lia. }
    assert (HfuelE_A : fuelE - 1 >= fuel_cost_tm A).
    { cbn [fuel_cost_tm] in HfuelE. lia. }
    
    (* Apply IHA to get extraction in b1 *)
    specialize (IHA b0 HfuelC_A Hdom0 Hcl0 Hnodup Htlt HfuelE_A).
    rewrite HA in IHA.
    
    (* Lift from b1 to b2 using preservation *)
    assert (Hpres12 : preserves_lt b1 b2).
    { unfold b1'.
      eapply preserves_lt_trans.
      - apply preserves_lt_put_fix_ty. simpl. rewrite Hv_eq. lia.
      - pose proof (compile_tm_preserves_lt fuelC (Some v :: ρ) body b1') as Hp.
        rewrite Hbody in Hp. exact Hp. }
    
    assert (HvA_lt_b1 : vA < RO.b_next b1).
    { rewrite <- HA. apply compile_tm_root_lt. }
    
    pose proof (extract_ext_inst b1 b2 (fix_env_of ρ) (RO.b_next b1) (fuelE - 2) 
                  Hpres12 Hcl1) as [Hexv12 _].
    
    (* Lift from b2 to b2' *)
    assert (Hpres22' : preserves_lt b2 b2').
    { unfold b2'. apply preserves_lt_put_fix_body. simpl. rewrite Hv_eq. lia. }
    
    assert (HvA_lt_b2 : vA < RO.b_next b2) by lia.
    
    pose proof (extract_ext_inst b2 b2' (fix_env_of ρ) (RO.b_next b2) (fuelE - 2)
                  Hpres22' Hcl2) as [Hexv22' _].
    
    rewrite <- (Hexv22' vA HvA_lt_b2).
    rewrite <- (Hexv12 vA HvA_lt_b1).
    exact IHA.
    
  - (* Body *)
    (* We need to show: EX.extract_v (fuelE - 2) b2' (<[v:=0]>(EX.env_shift (fix_env_of ρ))) vbody = body *)
    
    assert (HfuelC_body : fuelC >= S (T.size body)).
    { cbn [T.size] in HfuelC. lia. }
    assert (HfuelE_body : fuelE >= fuel_cost_tm body).
    { cbn [fuel_cost_tm] in HfuelE. lia. }
    
    (* We need fix_env_of (Some v :: ρ) = <[v:=0]>(EX.env_shift (fix_env_of ρ)) *)
    rewrite fix_env_of_cons_some.
    
    (* Apply IHbody to get extraction in b2 *)
    specialize (IHbody b1' HfuelC_body Hdom1' Hcl1' Hnodup_body Htlt_body HfuelE_body).
    rewrite Hbody in IHbody.
    
    (* Lift from b2 to b2' *)
    assert (Hpres22' : preserves_lt b2 b2').
    { unfold b2'. apply preserves_lt_put_fix_body. simpl. rewrite Hv_eq. lia. }
    
    assert (Hvbody_lt_b2 : vbody < RO.b_next b2).
    { rewrite <- Hbody. apply compile_tm_root_lt. }
    
    pose proof (extract_ext_inst b2 b2' (<[v:=0]>(EX.env_shift (fix_env_of ρ))) 
                  (RO.b_next b2) (fuelE - 2) Hpres22' Hcl2) as [Hexv22' _].
    
    rewrite <- (Hexv22' vbody Hvbody_lt_b2).
    exact IHbody.
Qed.

(** Compilation/extraction correctness (adequacy form).

    We separate:
    - `fuelC`: compilation fuel (for `ReadOff.compile_tm` / `compile_list`)
    - `fuelE`: extraction fuel (for `Extract.extract_v` / `extract_list`)

    The adequacy hypotheses `fuelE >= fuel_cost_tm t` / `fuelE >= fuel_cost_list ts`
    are intended to be strong enough to unfold `extract_v`/`extract_node` without
    relying on Coq reducing arithmetic expressions like `2 * S n`.
*)

Lemma extract_compile_tm_list_fuel_mutual (fuelC : nat) :
  (forall (fuelE : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder),
      fuelC >= compile_fuel_tm t ->
      dom_lt b ->
      closed_lt b (RO.b_next b) ->
      nodup_targets ρ ->
      targets_lt ρ (RO.b_next b) ->
      fuelE >= fuel_cost_tm t ->
      let '(v, b') := RO.compile_tm fuelC ρ t b in
      EX.extract_v fuelE b' (fix_env_of ρ) v = t)
  /\
  (forall (fuelE : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder),
      fuelC >= compile_fuel_list ts ->
      dom_lt b ->
      closed_lt b (RO.b_next b) ->
      nodup_targets ρ ->
      targets_lt ρ (RO.b_next b) ->
      fuelE >= fuel_cost_list ts ->
      let '(vs, b') := RO.compile_list fuelC ρ ts b in
      EX.extract_list EX.extract_v fuelE b' (fix_env_of ρ) vs = ts).
Proof.
  induction fuelC as [|fuelC IH].
  - split.
    + intros fuelE ρ t b HfuelC. exfalso.
      pose proof (compile_fuel_tm_ge_1 t) as Hge1. lia.
    + intros fuelE ρ ts b HfuelC Hdom Hcl Hnodup Htlt HfuelE.
      destruct ts as [|t ts]; cbn [compile_fuel_list] in HfuelC.
      * cbn [RO.compile_list EX.extract_list]. reflexivity.
      * exfalso.
        pose proof (compile_fuel_tm_ge_1 t) as Hge1. lia.
  - destruct IH as [IHtm IHlist].
    split.
    + intros fuelE ρ t b HfuelC Hdom Hcl Hnodup Htlt HfuelE.
      destruct t as
          [x
          |i
          |A B
          |A t0
          |t1 t2
          |A body
          |I0
          |I0 c0 params recs
          |I0 scrut C0 brs].
      * (* tVar *)
        eapply (extract_compile_tm_tVar_case fuelC fuelE ρ x b);
          try (eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC]);
          try exact Hdom; try exact Hcl; try exact Hnodup; try exact Htlt; try exact HfuelE.
      * (* tSort *)
        eapply (extract_compile_tm_tSort_case fuelC fuelE ρ i b);
          try (eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC]);
          try exact Hdom; try exact Hcl; try exact Hnodup; try exact Htlt; try exact HfuelE.
      * (* tPi *)
        (* derive subfuel bounds from compilation fuel *)
        assert (HfuelA : fuelC >= compile_fuel_tm A) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (HfuelB : fuelC >= compile_fuel_tm B) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        pose proof (fuel_cost_tPi_subterms A B fuelE HfuelE) as [HfuelEA HfuelEB].
        eapply (extract_compile_tm_tPi_case fuelC fuelE ρ A B b).
        -- intros b0 HfA Hdom0 Hcl0 Hnd0 Htlt0 HfuelEA'.
           apply (IHtm (fuelE - 2) ρ A b0 HfuelA Hdom0 Hcl0 Hnd0 Htlt0). exact HfuelEA'.
        -- intros b1 HfB Hdom1 Hcl1 Hnd1 Htlt1 HfuelEB'.
           apply (IHtm (fuelE - 2) (None :: ρ) B b1 HfuelB Hdom1 Hcl1 Hnd1 Htlt1). exact HfuelEB'.
        -- eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC].
        -- exact Hdom.
        -- exact Hcl.
        -- exact Hnodup.
        -- exact Htlt.
        -- exact HfuelE.
      * (* tLam *)
        assert (HfuelA : fuelC >= compile_fuel_tm A) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (Hfuelt : fuelC >= compile_fuel_tm t0) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        pose proof (fuel_cost_tLam_subterms A t0 fuelE HfuelE) as [HfuelEA HfuelEt].
        eapply (extract_compile_tm_tLam_case fuelC fuelE ρ A t0 b).
        -- intros b0 _ Hdom0 Hcl0 Hnd0 Htlt0 HfuelEA'.
           apply (IHtm (fuelE - 2) ρ A b0 HfuelA Hdom0 Hcl0 Hnd0 Htlt0). exact HfuelEA'.
        -- intros b1 _ Hdom1 Hcl1 Hnd1 Htlt1 HfuelEt'.
           apply (IHtm (fuelE - 2) (None :: ρ) t0 b1 Hfuelt Hdom1 Hcl1 Hnd1 Htlt1). exact HfuelEt'.
        -- eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC].
        -- exact Hdom.
        -- exact Hcl.
        -- exact Hnodup.
        -- exact Htlt.
        -- exact HfuelE.
      * (* tApp *)
        assert (Hfuel1 : fuelC >= compile_fuel_tm t1) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (Hfuel2 : fuelC >= compile_fuel_tm t2) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        pose proof (fuel_cost_tApp_subterms t1 t2 fuelE HfuelE) as [HfuelE1 HfuelE2].
        eapply (extract_compile_tm_tApp_case fuelC fuelE ρ t1 t2 b).
        -- intros b0 _ Hdom0 Hcl0 Hnd0 Htlt0 Hfuel1'.
           apply (IHtm (fuelE - 2) ρ t1 b0 Hfuel1 Hdom0 Hcl0 Hnd0 Htlt0). exact Hfuel1'.
        -- intros b1 _ Hdom1 Hcl1 Hnd1 Htlt1 Hfuel2'.
           apply (IHtm (fuelE - 2) ρ t2 b1 Hfuel2 Hdom1 Hcl1 Hnd1 Htlt1). exact Hfuel2'.
        -- (* IHlist for backlink args *)
           intros ts0 b0 HfuelTs Hdom0 Hcl0 Hnd0 Htlt0 HfuelTs'.
           apply (IHlist (fuelE - 2) ρ ts0 b0).
           { eapply Nat.le_trans; [apply compile_fuel_list_ge_list_size|]. exact HfuelTs. }
           all: try exact Hdom0; try exact Hcl0; try exact Hnd0; try exact Htlt0; exact HfuelTs'.
        -- eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC].
        -- exact Hdom.
        -- exact Hcl.
        -- exact Hnodup.
        -- exact Htlt.
        -- exact HfuelE.
      * (* tFix *)
        assert (HfuelA : fuelC >= compile_fuel_tm A) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (HfuelBody : fuelC >= compile_fuel_tm body) by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        pose proof (fuel_cost_tFix_subterms A body fuelE HfuelE) as [HfuelEA HfuelEbody].
        eapply (extract_compile_tm_tFix_case fuelC fuelE ρ A body b).
        -- intros b0 _ Hdom0 Hcl0 Hnd0 Htlt0 HfuelEA'.
           apply (IHtm (fuelE - 2) ρ A b0 HfuelA Hdom0 Hcl0 Hnd0 Htlt0). exact HfuelEA'.
        -- intros b1' _ Hdom1' Hcl1' Hnd1' Htlt1' HfuelEbody'.
           apply (IHtm (fuelE - 2) (Some (RO.b_next b) :: ρ) body b1' HfuelBody Hdom1' Hcl1' Hnd1' Htlt1'). exact HfuelEbody'.
        -- eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC].
        -- exact Hdom.
        -- exact Hcl.
        -- exact Hnodup.
        -- exact Htlt.
        -- exact HfuelE.
      * (* tInd *)
        eapply (extract_compile_tm_tInd_case fuelC fuelE ρ I0 b);
          try (eapply Nat.le_trans; [apply compile_fuel_tm_ge_size|exact HfuelC]);
          try exact Hdom; try exact Hcl; try exact Hnodup; try exact Htlt; try exact HfuelE.
      * (* tRoll *)
        cbn [RO.compile_tm].
        destruct (RO.compile_list fuelC ρ params b) as [vps b1] eqn:Hps.
        destruct (RO.compile_list fuelC ρ recs b1) as [vrs b2] eqn:Hrs.
        destruct (RO.fresh b2) as [v b3] eqn:Hfr.
        set (b4 := RO.put v (RO.nRoll I0 c0 (length vps) (length vrs)) (vps ++ vrs) b3).

        (* fuel for sublists *)
        assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 (T.tRoll I0 c0 params recs)); lia).
        assert (Hfuel_params : fuelE - 1 >= fuel_cost_list params) by (cbn [fuel_cost_tm] in HfuelE; lia).
        assert (Hfuel_recs : fuelE - 1 >= fuel_cost_list recs) by (cbn [fuel_cost_tm] in HfuelE; lia).

        (* invariants / target bounds after compiling params and recs *)
        pose proof (compile_list_dom_lt fuelC ρ params b Hdom) as Hdom1.
        rewrite Hps in Hdom1.
        pose proof (compile_list_closed fuelC ρ params b (conj Hdom Hcl) Htlt) as Hcl1.
        rewrite Hps in Hcl1.
        pose proof (compile_list_bnext_mono fuelC ρ params b) as Hmn1.
        rewrite Hps in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).

        pose proof (compile_list_dom_lt fuelC ρ recs b1 Hdom1) as Hdom2.
        rewrite Hrs in Hdom2.
        pose proof (compile_list_closed fuelC ρ recs b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
        rewrite Hrs in Hcl2.
        pose proof (compile_list_bnext_mono fuelC ρ recs b1) as Hmn2.
        rewrite Hrs in Hmn2. simpl in Hmn2.
        assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt1|exact Hmn2]).

        (* v is fresh => not in fix env *)
        assert (Hρv : fix_env_of ρ !! v = None).
        { unfold RO.fresh in Hfr. injection Hfr as <- _.
          apply fix_env_of_lookup_None_of_targets_lt. exact Htlt2. }

        (* show no fix metadata at v *)
        assert (Hfx2 : RO.b_fix_ty b2 !! v = None).
        { unfold RO.fresh in Hfr. injection Hfr as <- _.
          destruct (RO.b_fix_ty b2 !! RO.b_next b2) as [w|] eqn:Hfx; [|reflexivity].
          exfalso.
          destruct Hdom2 as [_ [_ [Hf _]]].
          specialize (Hf (RO.b_next b2) w Hfx).
          exact (Nat.lt_irrefl _ Hf). }
        assert (Hfx : RO.b_fix_ty b4 !! v = None).
        { unfold b4, RO.put. simpl.
          unfold RO.fresh in Hfr. simpl in Hfx2.
          exact Hfx2. }

        (* unfold extraction at root v *)
        rewrite (extract_v_unfold_ge2 fuelE b4 (fix_env_of ρ) v Hfuel_ge2).
        replace (fix_env_of ρ !! v) with (@None nat) by (symmetry; exact Hρv).
        replace (RO.b_fix_ty b4 !! v) with (@None nat) by (symmetry; exact Hfx).
        cbn.

        assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
        rewrite (extract_node_unfold_ge1 (fuelE - 1) b4 (fix_env_of ρ) v Hfuel_ge1).
        assert (Hnode : EX.lookup_node b4 v = RO.nRoll I0 c0 (length vps) (length vrs)).
        { unfold b4. apply lookup_node_put_eq. }
        assert (Hsucc : EX.lookup_succ b4 v = (vps ++ vrs)).
        { unfold b4. apply lookup_succ_put_eq. }
        rewrite Hnode, Hsucc.
        cbn.

        (* simplify take/drop splitting *)
        rewrite take_app.
        rewrite take_length.
        rewrite drop_app.
        rewrite drop_length.
        cbn [take drop].

        (* prove list extraction for params/recs, lifted to final builder *)
        assert (HfuelC_params : fuelC >= compile_fuel_list params)
          by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (HfuelC_recs : fuelC >= compile_fuel_list recs)
          by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).

        pose proof (IHlist (fuelE - 1) ρ params b HfuelC_params Hdom Hcl Hnodup Htlt Hfuel_params) as Hext_params.
        rewrite Hps in Hext_params.

        pose proof (IHlist (fuelE - 1) ρ recs b1 HfuelC_recs Hdom1 Hcl1 Hnodup Htlt1 Hfuel_recs) as Hext_recs.
        rewrite Hrs in Hext_recs.

        (* extensionality b1 -> b2 (recs compilation), and b2 -> b4 (fresh+put at v) *)
        pose proof (compile_list_preserves_lt fuelC ρ recs b1) as Hpres12.
        rewrite Hrs in Hpres12.
        pose proof (@extract_ext b1 b2 (RO.b_next b1) Hpres12 Hcl1 (fuelE - 1)) as [Hexv12 [Hexn12 [Hexs12 Hexl12]]].

        assert (Hagree24 : forall k,
                  k < v ->
                  b4.(RO.b_label) !! k = b2.(RO.b_label) !! k
                  /\ b4.(RO.b_succ) !! k = b2.(RO.b_succ) !! k
                  /\ b4.(RO.b_fix_ty) !! k = b2.(RO.b_fix_ty) !! k
                  /\ b4.(RO.b_fix_body) !! k = b2.(RO.b_fix_body) !! k).
        { intros k Hk.
          unfold b4, RO.put. simpl.
          unfold RO.fresh in Hfr. simpl.
          assert (k <> v) by lia.
          repeat split; try reflexivity; rewrite lookup_insert_ne; auto. }
        pose proof (@extract_ext b2 b4 v Hagree24 Hcl2 (fuelE - 1)) as [Hexv24 [Hexn24 [Hexs24 Hexl24]]].

        pose proof (compile_list_roots_lt fuelC ρ params b) as Hroots_params.
        rewrite Hps in Hroots_params. simpl in Hroots_params.
        pose proof (compile_list_roots_lt fuelC ρ recs b1) as Hroots_recs.
        rewrite Hrs in Hroots_recs. simpl in Hroots_recs.

        assert (Hfor_params_v : Forall (fun w => w < v) vps).
        { eapply Forall_impl; [|exact Hroots_params].
          intros w Hw.
          unfold RO.fresh in Hfr. injection Hfr as <- _.
          lia. }
        assert (Hfor_recs_v : Forall (fun w => w < v) vrs).
        { eapply Forall_impl; [|exact Hroots_recs].
          intros w Hw.
          unfold RO.fresh in Hfr. injection Hfr as <- _.
          lia. }

        (* params part *)
        rewrite <- (Hexl24 (fix_env_of ρ) vps Hfor_params_v).
        assert (Hfor_params_b1 : Forall (fun w => w < RO.b_next b1) vps) by exact Hroots_params.
        rewrite <- (Hexl12 (fix_env_of ρ) vps Hfor_params_b1).
        rewrite Hext_params.

        (* recs part *)
        rewrite <- (Hexl24 (fix_env_of ρ) vrs Hfor_recs_v).
        rewrite Hext_recs.

        reflexivity.

      * (* tCase *)
        cbn [RO.compile_tm].
        destruct (RO.compile_tm fuelC ρ scrut b) as [vscrut b1] eqn:Hscrut.
        destruct (RO.compile_tm fuelC ρ C0 b1) as [vC b2] eqn:HC.
        destruct (RO.compile_list fuelC ρ brs b2) as [vbrs b3] eqn:Hbrs.
        destruct (RO.fresh b3) as [v b4] eqn:Hfr.
        set (b5 := RO.put v (RO.nCase I0 (length vbrs)) ([vscrut; vC] ++ vbrs) b4).

        assert (Hfuel_ge2 : fuelE >= 2) by (pose proof (fuel_cost_tm_ge_2 (T.tCase I0 scrut C0 brs)); lia).
        assert (Hfuel_scrut : fuelE - 2 >= fuel_cost_tm scrut) by (cbn [fuel_cost_tm] in HfuelE; lia).
        assert (Hfuel_C : fuelE - 2 >= fuel_cost_tm C0) by (cbn [fuel_cost_tm] in HfuelE; lia).
        assert (Hfuel_brs : fuelE - 1 >= fuel_cost_list brs) by (cbn [fuel_cost_tm] in HfuelE; lia).

        (* invariants along compilation chain *)
        pose proof (compile_tm_dom_lt fuelC ρ scrut b Hdom) as Hdom1.
        rewrite Hscrut in Hdom1.
        pose proof (compile_tm_closed fuelC ρ scrut b (conj Hdom Hcl) Htlt) as Hcl1.
        rewrite Hscrut in Hcl1.
        pose proof (compile_tm_bnext_mono fuelC ρ scrut b) as Hmn1.
        rewrite Hscrut in Hmn1. simpl in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).

        pose proof (compile_tm_dom_lt fuelC ρ C0 b1 Hdom1) as Hdom2.
        rewrite HC in Hdom2.
        pose proof (compile_tm_closed fuelC ρ C0 b1 (conj Hdom1 Hcl1) Htlt1) as Hcl2.
        rewrite HC in Hcl2.
        pose proof (compile_tm_bnext_mono fuelC ρ C0 b1) as Hmn2.
        rewrite HC in Hmn2. simpl in Hmn2.
        assert (Htlt2 : targets_lt ρ (RO.b_next b2)) by (eapply targets_lt_mono; [exact Htlt1|exact Hmn2]).

        pose proof (compile_list_dom_lt fuelC ρ brs b2 Hdom2) as Hdom3.
        rewrite Hbrs in Hdom3.
        pose proof (compile_list_closed fuelC ρ brs b2 (conj Hdom2 Hcl2) Htlt2) as Hcl3.
        rewrite Hbrs in Hcl3.
        pose proof (compile_list_bnext_mono fuelC ρ brs b2) as Hmn3.
        rewrite Hbrs in Hmn3. simpl in Hmn3.
        assert (Htlt3 : targets_lt ρ (RO.b_next b3)) by (eapply targets_lt_mono; [exact Htlt2|exact Hmn3]).

        assert (Hρv : fix_env_of ρ !! v = None).
        { unfold RO.fresh in Hfr. injection Hfr as <- _.
          apply fix_env_of_lookup_None_of_targets_lt. exact Htlt3. }

        assert (Hfx3 : RO.b_fix_ty b3 !! v = None).
        { unfold RO.fresh in Hfr. injection Hfr as <- _.
          destruct (RO.b_fix_ty b3 !! RO.b_next b3) as [w|] eqn:Hfx; [|reflexivity].
          exfalso.
          destruct Hdom3 as [_ [_ [Hf _]]].
          specialize (Hf (RO.b_next b3) w Hfx).
          exact (Nat.lt_irrefl _ Hf). }
        assert (Hfx : RO.b_fix_ty b5 !! v = None).
        { unfold b5, RO.put. simpl.
          unfold RO.fresh in Hfr. simpl in Hfx3.
          exact Hfx3. }

        rewrite (extract_v_unfold_ge2 fuelE b5 (fix_env_of ρ) v Hfuel_ge2).
        replace (fix_env_of ρ !! v) with (@None nat) by (symmetry; exact Hρv).
        replace (RO.b_fix_ty b5 !! v) with (@None nat) by (symmetry; exact Hfx).
        cbn.

        assert (Hfuel_ge1 : fuelE - 1 >= 1) by lia.
        rewrite (extract_node_unfold_ge1 (fuelE - 1) b5 (fix_env_of ρ) v Hfuel_ge1).
        assert (Hnode : EX.lookup_node b5 v = RO.nCase I0 (length vbrs)).
        { unfold b5. apply lookup_node_put_eq. }
        assert (Hsucc : EX.lookup_succ b5 v = ([vscrut; vC] ++ vbrs)).
        { unfold b5. apply lookup_succ_put_eq. }
        rewrite Hnode, Hsucc.
        cbn.

        (* simplify take (length vbrs) vbrs *)
        rewrite take_length.

        (* prove scrut, C, and branches extraction, lifted to final builder *)
        assert (HfuelC_scrut : fuelC >= compile_fuel_tm scrut)
          by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (HfuelC_C : fuelC >= compile_fuel_tm C0)
          by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).
        assert (HfuelC_brs : fuelC >= compile_fuel_list brs)
          by (cbn [compile_fuel_tm RO.fuel_tm] in HfuelC; lia).

        pose proof (IHtm (fuelE - 2) ρ scrut b HfuelC_scrut Hdom Hcl Hnodup Htlt Hfuel_scrut) as Hext_scrut.
        rewrite Hscrut in Hext_scrut.

        pose proof (IHtm (fuelE - 2) ρ C0 b1 HfuelC_C Hdom1 Hcl1 Hnodup Htlt1 Hfuel_C) as Hext_C.
        rewrite HC in Hext_C.

        pose proof (IHlist (fuelE - 1) ρ brs b2 HfuelC_brs Hdom2 Hcl2 Hnodup Htlt2 Hfuel_brs) as Hext_brs.
        rewrite Hbrs in Hext_brs.

        (* extensionality lifts: b1->b2, b2->b3, b3->b5 *)
        pose proof (compile_tm_preserves_lt fuelC ρ C0 b1) as Hpres12.
        rewrite HC in Hpres12.
        pose proof (compile_list_preserves_lt fuelC ρ brs b2) as Hpres23.
        rewrite Hbrs in Hpres23.

        (* b3 -> b5 agrees below v *)
        assert (Hagree35 : forall k,
                  k < v ->
                  b5.(RO.b_label) !! k = b3.(RO.b_label) !! k
                  /\ b5.(RO.b_succ) !! k = b3.(RO.b_succ) !! k
                  /\ b5.(RO.b_fix_ty) !! k = b3.(RO.b_fix_ty) !! k
                  /\ b5.(RO.b_fix_body) !! k = b3.(RO.b_fix_body) !! k).
        { intros k Hk.
          unfold b5, RO.put. simpl.
          unfold RO.fresh in Hfr. simpl.
          assert (k <> v) by lia.
          repeat split; try reflexivity; rewrite lookup_insert_ne; auto. }

        pose proof (@extract_ext b1 b2 (RO.b_next b1) Hpres12 Hcl1 (fuelE - 2)) as [Hexv12 [Hexn12 [Hexs12 Hexl12]]].
        pose proof (@extract_ext b2 b3 (RO.b_next b2) (preserves_lt_fresh b2) Hcl2 (fuelE - 1)) as [Hexv23 [Hexn23 [Hexs23 Hexl23]]].
        pose proof (@extract_ext b3 b5 v Hagree35 Hcl3 (fuelE - 1)) as [Hexv35 [Hexn35 [Hexs35 Hexl35]]].

        (* lift scrut to final builder *)
        pose proof (compile_tm_root_lt fuelC ρ scrut b) as Hvs_lt.
        rewrite Hscrut in Hvs_lt.
        assert (Hvs_lt_b1 : vscrut < RO.b_next b1) by exact Hvs_lt.
        assert (Hvs_lt_v : vscrut < v).
        { unfold RO.fresh in Hfr. injection Hfr as <- _. lia. }
        rewrite <- (Hexv35 (fix_env_of ρ) vscrut Hvs_lt_v).
        (* b1 -> b3 lift via b2 and b3; easiest: note vscrut < b_next b1 < b_next b2 and use Hexv12 then Hexv23 *)
        assert (Hvs_lt_b2 : vscrut < RO.b_next b2) by (pose proof (compile_tm_bnext_mono fuelC ρ C0 b1); rewrite HC; simpl; lia).
        rewrite <- (Hexv23 (fix_env_of ρ) vscrut Hvs_lt_b2).
        rewrite <- (Hexv12 (fix_env_of ρ) vscrut Hvs_lt_b1).
        rewrite Hext_scrut.

        (* lift C to final builder *)
        pose proof (compile_tm_root_lt fuelC ρ C0 b1) as HvC_lt.
        rewrite HC in HvC_lt.
        assert (HvC_lt_b2 : vC < RO.b_next b2) by exact HvC_lt.
        assert (HvC_lt_v : vC < v).
        { unfold RO.fresh in Hfr. injection Hfr as <- _. lia. }
        rewrite <- (Hexv35 (fix_env_of ρ) vC HvC_lt_v).
        rewrite <- (Hexv23 (fix_env_of ρ) vC HvC_lt_b2).
        rewrite Hext_C.

        (* lift brs list to final builder *)
        pose proof (compile_list_roots_lt fuelC ρ brs b2) as Hroots_brs.
        rewrite Hbrs in Hroots_brs. simpl in Hroots_brs.
        assert (Hfor_brs_v : Forall (fun w => w < v) vbrs).
        { eapply Forall_impl; [|exact Hroots_brs].
          intros w Hw. unfold RO.fresh in Hfr. injection Hfr as <- _. lia. }
        rewrite <- (Hexl35 (fix_env_of ρ) vbrs Hfor_brs_v).
        rewrite <- (Hexl23 (fix_env_of ρ) vbrs Hroots_brs).
        rewrite Hext_brs.

        reflexivity.
    + (* list correctness *)
      intros fuelE ρ ts b HfuelC Hdom Hcl Hnodup Htlt HfuelE.
      destruct ts as [|t ts].
      * cbn [RO.compile_list EX.extract_list]. reflexivity.
      * cbn [RO.compile_list].
        destruct (RO.compile_tm fuelC ρ t b) as [v b1] eqn:Ht.
        destruct (RO.compile_list fuelC ρ ts b1) as [vs b2] eqn:Hts.
        cbn [EX.extract_list].
        pose proof (fuel_cost_list_subterms t ts fuelE HfuelE) as [Hfuel_t Hfuel_ts].
        assert (Hfuel_head : fuelC >= compile_fuel_tm t) by (cbn [compile_fuel_list compile_fuel_tm] in HfuelC; lia).
        assert (Hfuel_tail : fuelC >= compile_fuel_list ts) by (cbn [compile_fuel_list compile_fuel_tm] in HfuelC; lia).
        (* invariants for b1 *)
        pose proof (compile_tm_dom_lt fuelC ρ t b Hdom) as Hdom1.
        rewrite Ht in Hdom1.
        pose proof (compile_tm_closed fuelC ρ t b (conj Hdom Hcl) Htlt) as Hcl1.
        rewrite Ht in Hcl1.
        pose proof (compile_tm_bnext_mono fuelC ρ t b) as Hmn1.
        rewrite Ht in Hmn1.
        assert (Htlt1 : targets_lt ρ (RO.b_next b1)) by (eapply targets_lt_mono; [exact Htlt|exact Hmn1]).
        (* tail correctness in b2 *)
        pose proof (IHlist (fuelE - 1) ρ ts b1 Hfuel_tail Hdom1 Hcl1 Hnodup Htlt1 Hfuel_ts) as Hext_tail.
        rewrite Hts in Hext_tail.
        (* head correctness in b1, then lift to b2 *)
        pose proof (IHtm (fuelE - 1) ρ t b Hfuel_head Hdom Hcl Hnodup Htlt Hfuel_t) as Hext_head.
        rewrite Ht in Hext_head.
        (* lift extraction of v from b1 to b2 *)
        pose proof (compile_list_preserves_lt fuelC ρ ts b1) as Hpres12.
        rewrite Hts in Hpres12.
        pose proof (extract_ext_inst b1 b2 (fix_env_of ρ) (RO.b_next b1) (fuelE - 1) Hpres12 Hcl1) as [Hexv12 _].
        pose proof (compile_tm_root_lt fuelC ρ t b) as Hvlt.
        rewrite Ht in Hvlt.
        assert (Hv_in : v < RO.b_next b1) by (rewrite <- (compile_tm_root_lt fuelC ρ t b); rewrite Ht; exact Hvlt).
        rewrite <- (Hexv12 v Hv_in).
        rewrite Hext_head.
        f_equal.
        exact Hext_tail.
Qed.

Lemma extract_compile_tm
    (fuelC fuelE : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  fuelC >= compile_fuel_tm t ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm t ->
  let '(v, b') := RO.compile_tm fuelC ρ t b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = t.
Proof.
  exact (proj1 (extract_compile_tm_list_fuel_mutual fuelC)).
Qed.

Lemma extract_compile_list
    (fuelC fuelE : nat) (ρ : RO.back_env) (ts : list T.tm) (b : RO.builder) :
  fuelC >= compile_fuel_list ts ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_list ts ->
  let '(vs, b') := RO.compile_list fuelC ρ ts b in
  EX.extract_list EX.extract_v fuelE b' (fix_env_of ρ) vs = ts.
Proof.
  exact (proj2 (extract_compile_tm_list_fuel_mutual fuelC)).
Qed.

(** Adequacy: fuel_cost is bounded by syntactic size. *)

(* Helper: the bound holds for all terms, including nested in lists *)
Lemma fuel_cost_tm_le_2S_size (t : T.tm) :
  fuel_cost_tm t <= 2 * S (T.size t).
Proof.
  induction t as [x | i | A IHA B IHB | A IHA t IHt | t1 IH1 t2 IH2 | A IHA body IHbody | I | I c params IHparams recs IHrecs | I scrut IHscrut C IHC brs IHbrs].
  - (* tVar *)
    cbn. lia.
  - (* tSort *)
    cbn. lia.
  - (* tPi *)
    cbn [fuel_cost_tm T.size].
    lia.
  - (* tLam *)
    cbn [fuel_cost_tm T.size].
    lia.
  - (* tApp *)
    cbn [fuel_cost_tm T.size].
    lia.
  - (* tFix *)
    cbn [fuel_cost_tm T.size].
    lia.
  - (* tInd *)
    cbn. lia.
  - (* tRoll *)
    cbn [fuel_cost_tm T.size].
    assert (Hparams : fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 params
                      <= 2 * fold_right (fun u n => T.size u + n) 0 params).
    { clear IHrecs recs.
      induction params as [|p params IHp].
      - simpl. lia.
      - simpl.
        assert (Hp : fuel_cost_tm p <= 2 * S (T.size p)) by (apply IHparams; simpl; auto).
        lia. }
    assert (Hrecs : fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 recs
                    <= 2 * fold_right (fun u n => T.size u + n) 0 recs).
    { clear IHparams params Hparams.
      induction recs as [|r recs IHr].
      - simpl. lia.
      - simpl.
        assert (Hr : fuel_cost_tm r <= 2 * S (T.size r)) by (apply IHrecs; simpl; auto).
        lia. }
    lia.
  - (* tCase *)
    cbn [fuel_cost_tm T.size].
    assert (Hbrs : fold_right (fun u n => 1 + fuel_cost_tm u + n) 0 brs
                   <= 2 * fold_right (fun u n => T.size u + n) 0 brs).
    { clear IHscrut scrut IHC C.
      induction brs as [|br brs IHbr].
      - simpl. lia.
      - simpl.
        assert (Hbr : fuel_cost_tm br <= 2 * S (T.size br)) by (apply IHbrs; simpl; auto).
        lia. }
    lia.
Qed.

Lemma fuel_cost_list_le_2fold (ts : list T.tm) :
  fuel_cost_list ts <= 2 * fold_right (fun u n => T.size u + n) 0 ts.
Proof.
  induction ts as [|t ts IH].
  - simpl. lia.
  - simpl.
    assert (Ht : fuel_cost_tm t <= 2 * S (T.size t)).
    { apply fuel_cost_tm_le_2S_size. }
    lia.
Qed.

(*** Round-trip theorems. ***)

Theorem extract_read_off_id (t : T.tm) : EX.extract_read_off t = t.
Proof.
  unfold EX.extract_read_off.
  destruct (RO.read_off_raw t) as [root b] eqn:Hreadoff.
  unfold RO.read_off_raw in Hreadoff.
  (* read_off_raw compiles with fuel = RO.fuel_tm t, empty back-env, empty builder *)
  assert (Hcompile : RO.compile_tm (RO.fuel_tm t) [] t RO.empty_builder = (root, b)).
  { unfold RO.read_off_raw in Hreadoff. exact Hreadoff. }
  
  (* Apply extract_compile_tm with adequacy *)
  pose proof (extract_compile_tm (RO.fuel_tm t) (2 * S (T.size t)) [] t RO.empty_builder) as Hext.
  
  (* Discharge compilation fuel hypothesis *)
  assert (HfuelC : RO.fuel_tm t >= compile_fuel_tm t) by reflexivity.
  
  (* Discharge invariants for empty builder *)
  assert (Hdom : dom_lt RO.empty_builder).
  { unfold dom_lt, RO.empty_builder. simpl.
    repeat split; intros; rewrite lookup_empty in *; discriminate. }
  
  assert (Hcl : closed_lt RO.empty_builder (RO.b_next RO.empty_builder)).
  { unfold closed_lt, RO.empty_builder. simpl.
    repeat split; intros; rewrite lookup_empty in *; discriminate. }
  
  assert (Hnodup : nodup_targets []).
  { unfold nodup_targets. constructor. }
  
  assert (Htlt : targets_lt [] (RO.b_next RO.empty_builder)).
  { apply targets_lt_nil. }
  
  (* Discharge extraction fuel adequacy using the bridge lemma *)
  assert (HfuelE : 2 * S (T.size t) >= fuel_cost_tm t).
  { pose proof (fuel_cost_tm_le_2S_size t). lia. }
  
  (* Apply the main lemma *)
  specialize (Hext HfuelC Hdom Hcl Hnodup Htlt HfuelE).
  rewrite Hcompile in Hext.
  exact Hext.
Qed.

Theorem extract_read_off_ciu
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
  CIUJudgement.ciu_jTy Σenv Γ t (EX.extract_read_off t) A.
Proof.
  apply CIUJudgement.ciu_jTy_of_eq.
  symmetry.
  apply extract_read_off_id.
Qed.


(** Round-trip correctness for tVar. *)
Lemma extract_compile_tm_tVar_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (x : nat) (b : RO.builder) :
  S fuelC >= S (T.size (T.tVar x)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tVar x) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tVar x) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tVar x.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.
  
  (* Unfold compilation of tVar *)
  cbn [RO.compile_tm].
  destruct (RO.fresh b) as [v b0] eqn:Hfr.
  set (b' := RO.put v (RO.nVar x) [] b0).
  
  (* Unfold extraction *)
  apply extract_v_unfold_ge2.
  { cbn [fuel_cost_tm] in HfuelE. lia. }
  
  cbn [EX.extract_v].
  
  (* Show v is not in fix_env_of ρ *)
  assert (Hv_not_in : fix_env_of ρ !! v = None).
  { unfold RO.fresh in Hfr. injection Hfr as <- _.
    apply fix_env_of_lookup_None_of_targets_lt. exact Htlt. }
  rewrite Hv_not_in.
  
  (* Show v has no fix_ty *)
  assert (Hno_fix : RO.b_fix_ty b' !! v = None).
  { unfold b', RO.put. simpl.
    unfold RO.fresh in Hfr. injection Hfr as <- _.
    destruct Hdom as [_ [_ [Hf _]]].
    destruct (RO.b_fix_ty b0 !! (RO.b_next b)) as [w|] eqn:E; [|reflexivity].
    exfalso.
    assert (Hdom0 : dom_lt b0) by (rewrite Hfr; apply dom_lt_fresh; exact Hdom).
    destruct Hdom0 as [_ [_ [Hf0 _]]].
    specialize (Hf0 (RO.b_next b) w E).
    rewrite Hfr in Hf0. simpl in Hf0. lia. }
  rewrite Hno_fix.
  
  (* Now we're in extract_node *)
  apply extract_node_unfold_ge1.
  { cbn [fuel_cost_tm] in HfuelE. lia. }
  
  cbn [EX.extract_node].
  unfold EX.lookup_node.
  unfold b', RO.put. simpl.
  rewrite lookup_insert.
  rewrite decide_True by reflexivity.
  reflexivity.
Qed.

(** Round-trip correctness for tSort. *)
Lemma extract_compile_tm_tSort_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (i : nat) (b : RO.builder) :
  S fuelC >= S (T.size (T.tSort i)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tSort i) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tSort i) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tSort i.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.
  
  (* Unfold compilation of tSort *)
  cbn [RO.compile_tm].
  destruct (RO.fresh b) as [v b0] eqn:Hfr.
  set (b' := RO.put v (RO.nSort i) [] b0).
  
  (* Unfold extraction *)
  apply extract_v_unfold_ge2.
  { cbn [fuel_cost_tm] in HfuelE. lia. }
  
  cbn [EX.extract_v].
  
  (* Show v is not in fix_env_of ρ *)
  assert (Hv_not_in : fix_env_of ρ !! v = None).
  { unfold RO.fresh in Hfr. injection Hfr as <- _.
    apply fix_env_of_lookup_None_of_targets_lt. exact Htlt. }
  rewrite Hv_not_in.
  
  (* Show v has no fix_ty *)
  assert (Hno_fix : RO.b_fix_ty b' !! v = None).
  { unfold b', RO.put. simpl.
    unfold RO.fresh in Hfr. injection Hfr as <- _.
    destruct Hdom as [_ [_ [Hf _]]].
    destruct (RO.b_fix_ty b0 !! (RO.b_next b)) as [w|] eqn:E; [|reflexivity].
    exfalso.
    assert (Hdom0 : dom_lt b0) by (rewrite Hfr; apply dom_lt_fresh; exact Hdom).
    destruct Hdom0 as [_ [_ [Hf0 _]]].
    specialize (Hf0 (RO.b_next b) w E).
    rewrite Hfr in Hf0. simpl in Hf0. lia. }
  rewrite Hno_fix.
  
  (* Now we're in extract_node *)
  apply extract_node_unfold_ge1.
  { cbn [fuel_cost_tm] in HfuelE. lia. }
  
  cbn [EX.extract_node].
  unfold EX.lookup_node.
  unfold b', RO.put. simpl.
  rewrite lookup_insert.
  rewrite decide_True by reflexivity.
  reflexivity.
Qed.

(** Round-trip correctness for tInd. *)
Lemma extract_compile_tm_tInd_case
    (fuelC fuelE : nat) (ρ : RO.back_env) (I : nat) (b : RO.builder) :
  S fuelC >= S (T.size (T.tInd I)) ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  fuelE >= fuel_cost_tm (T.tInd I) ->
  let '(v, b') := RO.compile_tm (S fuelC) ρ (T.tInd I) b in
  EX.extract_v fuelE b' (fix_env_of ρ) v = T.tInd I.
Proof.
  intros HfuelC Hdom Hcl Hnodup Htlt HfuelE.

  cbn [RO.compile_tm].
  destruct (RO.fresh b) as [v b0] eqn:Hfr.
  set (b' := RO.put v (RO.nInd I) [] b0).

  apply extract_v_unfold_ge2.
  { cbn [fuel_cost_tm] in HfuelE. lia. }

  cbn [EX.extract_v].

  assert (Hv_not_in : fix_env_of ρ !! v = None).
  { unfold RO.fresh in Hfr. injection Hfr as <- _.
    apply fix_env_of_lookup_None_of_targets_lt. exact Htlt. }
  rewrite Hv_not_in.

  assert (Hno_fix : RO.b_fix_ty b' !! v = None).
  { unfold b', RO.put. simpl.
    unfold RO.fresh in Hfr. injection Hfr as <- _.
    destruct (RO.b_fix_ty b0 !! (RO.b_next b)) as [w|] eqn:E; [|reflexivity].
    exfalso.
    assert (Hdom0 : dom_lt b0) by (rewrite Hfr; apply dom_lt_fresh; exact Hdom).
    destruct Hdom0 as [_ [_ [Hf0 _]]].
    specialize (Hf0 (RO.b_next b) w E).
    rewrite Hfr in Hf0. simpl in Hf0. lia. }
  rewrite Hno_fix.

  apply extract_node_unfold_ge1.
  { cbn [fuel_cost_tm] in HfuelE. lia. }

  cbn [EX.extract_node].
  unfold EX.lookup_node.
  unfold b', RO.put. simpl.
  rewrite lookup_insert.
  rewrite decide_True by reflexivity.
  reflexivity.
Qed.
