From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Equiv Require Import CIU.
Import Term.Syntax.
Import ListNotations.
Set Default Proof Using "Type".

(** Non-invertibility of case-splitting on neutral scrutinees.

    We prove: committing to a single branch of a case-split on a neutral
    variable is unsound.  Concretely, reducing

        case x of {nil → 0; cons y ys → 1} : Nat

    to only the nil branch (residual = 0) produces a program that is
    NOT CIU-equivalent to the source, because for inputs where x is
    non-nil, the source evaluates to 1 but the residual evaluates to 0.

    This proves that the split rule is genuinely non-invertible:
    the conclusion (case expression) does NOT imply each premise
    individually.  The synchronous phase must explore all branches.
*)

(** Counterexample term:
    case x of {nil → 0; cons y ys → 1}
    where x = tVar 0 (neutral, of type List) *)
Definition case_ex : tm :=
  tCase 1                            (* List = inductive 1 *)
    (tVar 0)                         (* scrutinee: neutral variable *)
    Examples.nat_ty                   (* motive: Nat *)
    [ Examples.zero;                  (* nil branch: 0 *)
      tLam Examples.nat_ty           (* cons branch: bound y *)
        (tLam ListNat.list_ty        (* bound ys *)
          (Examples.succ Examples.zero))  (* result: 1 *)
    ].

(** The source term: case_ex *)
Definition source : tm := case_ex.

(** The "eager nil branch" residual: just 0 *)
Definition eager_nil : tm := Examples.zero.

(** Closing substitution: x ↦ cons 0 nil *)
Definition σ : nat -> tm :=
  fun n => match n with
  | 0 => ListNat.cons Examples.zero ListNat.nil
  | _ => tVar n
  end.

(** Source evaluates to 1 *)
Lemma source_eval :
  terminates_to (source.[σ]) (Examples.succ Examples.zero).
Proof.
  unfold source, case_ex.
  asimpl.
  eapply terminates_to_steps; [|split; [apply rt_refl|constructor]].
  apply rt_step. apply step_case_roll.
  reflexivity.
Qed.

(** Eager nil residual evaluates to 0 *)
Lemma eager_nil_eval :
  terminates_to (eager_nil.[σ]) Examples.zero.
Proof.
  unfold eager_nil.
  asimpl.
  split; [apply rt_refl|constructor].
Qed.

(** The two are not CIU-equivalent: the same closing substitution
    produces different values (succ zero ≠ zero). *)
Theorem split_not_invertible_by_counterexample :
  ~ ciu source eager_nil.
Proof.
  intro Hciu.
  destruct Hciu as [Hto _].
  pose proof (Hto σ (Examples.succ Examples.zero) source_eval).
  (* H : terminates_to (eager_nil.[σ]) (succ zero) *)
  (* But eager_nil_eval says eager_nil.[σ] terminates_to zero *)
  pose proof (Cbn.terminates_to_det _ _ _ H eager_nil_eval).
  (* succ zero = zero — contradiction *)
  discriminate.
Qed.

(** Stronger statement: the split rule is non-invertible.
    The case expression is CIU-equivalent to itself (trivially),
    but committing to one branch produces a non-equivalent term. *)
Theorem split_rule_non_invertible :
  ciu source source  (* the conclusion is provable *)
  /\
  ~ ciu source eager_nil. (* but one premise alone is not *)
Proof.
  split.
  - apply ciu_refl.
  - apply split_not_invertible_by_counterexample.
Qed.
