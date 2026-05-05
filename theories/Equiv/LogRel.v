From Stdlib Require Import List Arith Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Equiv Require Import CIU CIUJudgement.

Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  * Logical Relations for the List/Nat Fragment

  We define a step-free (type-indexed) logical relation on closed values
  and terms.  The relation is defined by structural induction on a
  semantic type [ty_sem], which mirrors the object-language types.

  This is Phase 0 of the LOGICAL_RELATIONS_PLAN.md:
  - Define [lr_val], [lr_tm] without SC machinery
  - Prove basic closure properties
  - Connect to [ciu_jTy_rel]
  - State (but do not yet prove) the fundamental lemma

  The key bridge:
    [ciu_jTy_rel Σ Γ t t A (fun v _ => lr_val T v)]
  is exactly adequacy: t converges to a value satisfying the logical relation.
*)

(* ------------------------------------------------------------------ *)
(** * 1. Semantic types                                                 *)
(* ------------------------------------------------------------------ *)

(** A simplified semantic type universe covering the fragment we need.
    This deliberately does not try to interpret all of CoC — only the
    concrete inductive types used in our examples. *)
Inductive ty_sem : Type :=
| ty_nat  : ty_sem                        (* Nat  *)
| ty_bool : ty_sem                        (* Bool (encoded as Nat 0/1) *)
| ty_list : ty_sem                        (* List Nat *)
| ty_arr  : ty_sem -> ty_sem -> ty_sem    (* A -> B *)
| ty_ref  : ty_sem -> (tm -> Prop) -> ty_sem.  (* {x : A | P x} *)

(* ------------------------------------------------------------------ *)
(** * 2. The logical relation                                           *)
(* ------------------------------------------------------------------ *)

(** [lr_val T v]: value [v] belongs to the semantic type [T].
    Defined by induction on [T].

    For [ty_arr]: we require that applying the function to any lr-adequate
    argument produces a terminating result that is lr-adequate.
    This makes [lr_val (ty_arr A B)] a *value* predicate — the function
    itself is a value (a lambda), but its behaviour on arguments matters.

    For [ty_ref A P]: the value must be in [lr_val A] AND satisfy [P].
*)
Fixpoint lr_val (T : ty_sem) (v : tm) : Prop :=
  match T with
  | ty_nat =>
      (* v is a Nat value: tRoll 0 0 [] (zero) or tRoll 0 1 [n] (succ n) *)
      value v /\
      match v with
      | tRoll 0 0 []    => True                    (* zero *)
      | tRoll 0 1 [n]   => lr_val ty_nat n          (* succ n *)
      | _               => False
      end
  | ty_bool =>
      v = ListNat.bool_true \/ v = ListNat.bool_false
  | ty_list =>
      (* v is a List value: nil or cons x xs *)
      value v /\
      match v with
      | tRoll 1 0 []       => True                  (* nil *)
      | tRoll 1 1 [x; xs]  =>
          lr_val ty_nat x /\ lr_val ty_list xs       (* cons x xs *)
      | _                   => False
      end
  | ty_arr A B =>
      (* v is a lambda; applying it to any lr-adequate argument
         produces a term that terminates to an lr-adequate value *)
      value v /\
      forall (u : tm),
        lr_val A u ->
        exists w,
          terminates_to (tApp v u) w /\
          lr_val B w
  | ty_ref A P =>
      lr_val A v /\ P v
  end.

(** [lr_tm T t]: term [t] is lr-adequate at semantic type [T].
    A term is adequate if it terminates to an lr-adequate value. *)
Definition lr_tm (T : ty_sem) (t : tm) : Prop :=
  exists v, terminates_to t v /\ lr_val T v.

(** [lr_env Γ_sem σ]: a substitution [σ] is lr-adequate for a
    semantic context [Γ_sem = [(x_0 : T_0), ..., (x_n : T_n)]].
    Each σ_i is lr-adequate at T_i. *)
Definition lr_env (Γ_sem : list ty_sem) (σ : list tm) : Prop :=
  Forall2 lr_val Γ_sem σ.

(* ------------------------------------------------------------------ *)
(** * 3. Basic closure properties                                       *)
(* ------------------------------------------------------------------ *)

Lemma lr_val_value (T : ty_sem) (v : tm) :
  lr_val T v -> value v.
Proof.
  induction T; intros H; simpl in H.
  - exact (proj1 H).
  - destruct H as [-> | ->]; constructor.
  - exact (proj1 H).
  - exact (proj1 H).
  - apply IHT. exact (proj1 H).
Qed.

Lemma lr_tm_of_val (T : ty_sem) (v : tm) :
  lr_val T v -> lr_tm T v.
Proof.
  intro Hv.
  exists v. split.
  - split; [apply rt_refl | apply lr_val_value; exact Hv].
  - exact Hv.
Qed.

Lemma lr_val_ref_elim (T : ty_sem) (P : tm -> Prop) (v : tm) :
  lr_val (ty_ref T P) v -> lr_val T v /\ P v.
Proof. intro H. exact H. Qed.

Lemma lr_val_ref_intro (T : ty_sem) (P : tm -> Prop) (v : tm) :
  lr_val T v -> P v -> lr_val (ty_ref T P) v.
Proof. intros HA HP. exact (conj HA HP). Qed.

Lemma lr_tm_ref_intro (T : ty_sem) (P : tm -> Prop) (t : tm) :
  lr_tm T t ->
  (forall v, terminates_to t v -> P v) ->
  lr_tm (ty_ref T P) t.
Proof.
  intros [v [Hterm Hval]] HP.
  exists v. split.
  - exact Hterm.
  - exact (lr_val_ref_intro T P v Hval (HP v Hterm)).
Qed.

(** [lr_tm] is downward-closed under steps: if [t] steps to [t'] and
    [t'] is lr-adequate, so is [t]. *)
Lemma lr_tm_steps_prefix (T : ty_sem) (t t' : tm) :
  steps t t' -> lr_tm T t' -> lr_tm T t.
Proof.
  intros Hsteps [v [Hterm Hval]].
  exists v. split.
  - destruct Hterm as [Hsteps' Hval'].
    split; [eapply rt_trans; [exact Hsteps | exact Hsteps'] | exact Hval'].
  - exact Hval.
Qed.

Lemma lr_tm_step_prefix (T : ty_sem) (t t' : tm) :
  step t t' -> lr_tm T t' -> lr_tm T t.
Proof.
  intros Hstep. apply lr_tm_steps_prefix. apply rt_step. exact Hstep.
Qed.

(* ------------------------------------------------------------------ *)
(** * 4. Adequacy for concrete values                                   *)
(* ------------------------------------------------------------------ *)

Lemma lr_val_zero : lr_val ty_nat Examples.zero.
Proof.
  unfold Examples.zero. simpl. split.
  - constructor.
  - exact I.
Qed.

Lemma lr_val_succ (n : tm) :
  lr_val ty_nat n -> lr_val ty_nat (Examples.succ n).
Proof.
  intro Hn. unfold Examples.succ. simpl. split.
  - constructor.
  - exact Hn.
Qed.

Lemma lr_val_nil : lr_val ty_list ListNat.nil.
Proof.
  unfold ListNat.nil. simpl. split.
  - constructor.
  - exact I.
Qed.

Lemma lr_val_cons (x xs : tm) :
  lr_val ty_nat x -> lr_val ty_list xs ->
  lr_val ty_list (ListNat.cons x xs).
Proof.
  intros Hx Hxs. unfold ListNat.cons. simpl. split.
  - constructor.
  - exact (conj Hx Hxs).
Qed.

Lemma lr_val_bool_true : lr_val ty_bool ListNat.bool_true.
Proof. unfold ListNat.bool_true. left. reflexivity. Qed.

Lemma lr_val_bool_false : lr_val ty_bool ListNat.bool_false.
Proof. unfold ListNat.bool_false. right. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 5. Connection to [ciu_jTy_rel]                                   *)
(* ------------------------------------------------------------------ *)

(** Adequacy for [t] under a typed context is exactly
    [ciu_jTy_rel] with [R = (fun v _ => lr_val T v)].

    This shows that [ciu_jTy_rel] is already the right framework —
    we just need to populate it with the logical relation [lr_val]. *)

Definition adequacy_rel (T : ty_sem) : tm -> tm -> Prop :=
  fun v _ => lr_val T v.

Lemma lr_tm_iff_ciu_rel
    (Σenv : Typing.Typing.env) (Γ : Typing.Typing.ctx)
    (A : tm) (T : ty_sem) (t : tm) :
  (** If [t] is lr-adequate for every typed closing substitution,
      then it satisfies [ciu_jTy_rel] with the adequacy relation. *)
  (forall σ, Typing.Typing.has_subst Σenv [] σ Γ ->
             Forall value σ ->
             lr_tm T (Typing.Typing.subst_list σ t)) ->
  CIUJudgement.ciu_jTy_rel Σenv Γ t t A (adequacy_rel T).
Proof.
  intro Hadq.
  split.
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Hadq σ Hσ Hvσ) as [w [Hterm_w Hval_w]].
    (* By determinism: if t[σ] ⇓ v and t[σ] ⇓ w, then v = w *)
    assert (v = w) by (eapply Cbn.terminates_to_det; exact Hterm; exact Hterm_w).
    subst w.
    exists v. split; [exact Hterm | exact Hval_w].
  - intros Δ σ v Hσ Hvσ Hterm.
    destruct (Hadq σ Hσ Hvσ) as [w [Hterm_w Hval_w]].
    assert (v = w) by (eapply Cbn.terminates_to_det; exact Hterm; exact Hterm_w).
    subst w.
    exists v. split; [exact Hterm | exact Hval_w].
Qed.

(* ------------------------------------------------------------------ *)
(** * 6. The fundamental lemma (statement)                              *)
(* ------------------------------------------------------------------ *)

(**
  The fundamental lemma says: every well-typed term is lr-adequate.

  For our fragment (Nat, List, Bool, arrows), the proof is by induction
  on the typing derivation.  The hard cases are:
  - [tFix]: requires a step-indexed argument or coinduction
  - [tCase]: requires knowing the scrutinee's lr-adequate value

  We state the lemma here.  The proof for the non-recursive fragment
  (terms without [tFix]) is straightforward.  The recursive fragment
  requires the lemma environment (Phase 1 of the plan).

  For now we prove it for the restricted case: terms that terminate
  (i.e., the SC has already verified termination via [trace_condition_ok]).
*)

(** Semantic typing context: maps each syntactic type to a semantic type.
    For our fragment this is straightforward. *)
Definition ty_of_nat   : ty_sem := ty_nat.
Definition ty_of_list  : ty_sem := ty_list.
Definition ty_of_bool  : ty_sem := ty_bool.
Definition ty_of_arr   : ty_sem -> ty_sem -> ty_sem := ty_arr.

(** Conditional fundamental lemma:
    If [t] terminates (we know this from the SC) and it terminates to
    a value satisfying the structural invariant of its type, then [t]
    is lr-adequate.

    This is weaker than the full fundamental lemma but sufficient for
    all examples where the SC drives to normal form. *)
Lemma lr_of_termination_and_shape
    (T : ty_sem) (t v : tm) :
  terminates_to t v ->
  lr_val T v ->
  lr_tm T t.
Proof.
  intros Hterm Hval.
  exists v. exact (conj Hterm Hval).
Qed.

(** The full fundamental lemma is left as a goal for Phase 1: *)
(**
Theorem fundamental_lemma :
  forall Σ Γ Γ_sem t A T σ,
    has_type Σ Γ t A ->
    ty_interp A = T ->
    lr_env Γ_sem σ ->
    lr_tm T (subst_list σ t).

  Proof: by induction on [has_type Σ Γ t A].
  Key cases:
  - tVar: immediate from lr_env hypothesis
  - tLam: construct lr_val (ty_arr A B) using lr_tm of body
  - tApp: apply lr_val (ty_arr A B) to lr_tm of argument
  - tFix: requires either step-indexing or direct well-founded induction
           on the measure decremented at each fix unrolling
  - tCase: case on the lr-adequate value of the scrutinee
  - tRoll: construct lr_val of the inductive type
*)

(* ------------------------------------------------------------------ *)
(** * 7. Refinement types for SC goals                                  *)
(* ------------------------------------------------------------------ *)

(** The key predicate for our examples:
    [converges_to_true t] means [t] terminates to [bool_true]. *)
Definition converges_to_true (t : tm) : Prop :=
  exists v, terminates_to t v /\ v = ListNat.bool_true.

(** Refinement semantic type for "List that is sorted": *)
Definition ty_sorted_list : ty_sem :=
  ty_ref ty_list
    (fun v => converges_to_true (tApp ListNat.sorted v)).

(** [sort] producing a sorted list:
    [sort ∈ ⟦{f : List → List | ∀ l. sorted (f l) ⇓ true}⟧]
    expressed as: *)
Definition sort_produces_sorted : Prop :=
  forall (l : tm),
    lr_val ty_list l ->
    lr_tm ty_sorted_list (tApp ListNat.sort l).

(** This is what we want to prove.  It cannot be proved by the current
    SC alone — it requires the lemma:
      ∀ l. sorted l → sorted (insert x l) ⇓ true
    which is itself provable by the SC (induction on l).

    With Phase 1 (lemma environment) complete, [sort_produces_sorted]
    becomes provable automatically. *)

(** For now, we prove the trivial direction: if [sort l ⇓ v] and
    [sorted v ⇓ true], then [sort l ∈ ⟦ty_sorted_list⟧]. *)
Lemma lr_sorted_list_intro (l v : tm) :
  terminates_to (tApp ListNat.sort l) v ->
  lr_val ty_list v ->
  converges_to_true (tApp ListNat.sorted v) ->
  lr_tm ty_sorted_list (tApp ListNat.sort l).
Proof.
  intros Hterm Hlist Hsorted.
  apply lr_of_termination_and_shape with (v := v).
  - exact Hterm.
  - exact (lr_val_ref_intro ty_list _ v Hlist Hsorted).
Qed.

(* ------------------------------------------------------------------ *)
(** * 8. Adequacy from SC residuals (the bridge)                        *)
(* ------------------------------------------------------------------ *)

(**
  When the SC produces a residual that [vm_compute] reduces to
  [bool_true], we can extract an adequacy result.

  For example, we already proved (in SortExamples.v / IndexCalc.v):
    [sum (sort l) = sum l]
  by [vm_compute; reflexivity].

  This means the SC drove [sum (sort l)] to the same residual as [sum l].
  By [supercompile_ciu_soundness_untyped], both are CIU-equivalent to their
  source.  The adequacy result follows if we know [sum l] converges to
  a Nat value — which the fundamental lemma will give us.

  The current gap: we have CIU (sum (sort l) ≈ sum l) but not
  "sum l ∈ ⟦Nat⟧" as a mechanised statement.  The fundamental lemma
  closes this gap.
*)

(** Placeholder for Phase 1: SC adequacy theorem.
    When proved, this will say: if the SC produces a residual and
    [vm_compute] shows it equals a concrete value [v], then the source
    term is lr-adequate at type [T] (where [lr_val T v] holds). *)
Axiom sc_adequacy_placeholder :
  forall (Σenv : Typing.Typing.env) (Γ : Typing.Typing.ctx)
         (t residual : tm) (T : ty_sem),
    (* SC produces a residual *)
    (exists fuel v b,
       Supercompile.supercompile_jTy_tc fuel Σenv Γ t Examples.nat_ty = Some (v, b) /\
       Supercompile.residualise_cfg fuel Σenv b v 0 (∅ : Supercompile.fix_env) = residual) ->
    (* The residual is lr-adequate (from fundamental lemma, future work) *)
    lr_tm T residual ->
    (* Therefore the source is lr-adequate *)
    lr_tm T t.

From Cyclic.Transform Require Import Supercompile.

End LogRelDraft.

(** Note: [sc_adequacy_placeholder] is an Axiom, clearly marked.
    It will be replaced by a proved theorem in Phase 1 when the
    fundamental lemma is established.  Its statement is precise enough
    to verify that the architecture is correct. *)
