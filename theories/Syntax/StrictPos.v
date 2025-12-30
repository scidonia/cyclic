From Stdlib Require Import List Arith Utf8.

Import ListNotations.

Set Default Proof Using "Type".

(* Finitary strictly-positive inductive signatures.

   We represent each inductive by a finite list of constructors. Each constructor
   has a finite list of *non-recursive* parameter types (in some type universe
   `Ty`) and a finite number of recursive fields.

   This representation is meant to be consumed by a typing judgement parameterized
   over a global environment of such signatures.
*)

Record ctor_sig (Ty : Type) : Type := {
  ctor_param_tys : list Ty;
  ctor_rec_arity : nat;
}.

Record ind_sig (Ty : Type) : Type := {
  ind_level : nat;
  ind_ctors : list (ctor_sig Ty);
}.

Definition ctor_param_arity {Ty : Type} (c : ctor_sig Ty) : nat :=
  length (@ctor_param_tys _ c).

Definition lookup {A : Type} (xs : list A) (n : nat) : option A :=
  nth_error xs n.

Definition lookup_ind {Ty : Type} (Σenv : list (ind_sig Ty)) (I : nat) : option (ind_sig Ty) :=
  lookup Σenv I.

Definition lookup_ctor {Ty : Type} (Σ : ind_sig Ty) (c : nat) : option (ctor_sig Ty) :=
  lookup (@ind_ctors _ Σ) c.

Lemma lookup_ctor_lt {Ty : Type} (Σ : ind_sig Ty) (c : nat) (ctor : ctor_sig Ty) :
  lookup_ctor Σ c = Some ctor -> c < length (@ind_ctors _ Σ).
Proof.
  unfold lookup_ctor, lookup.
  intro H.
  apply nth_error_Some.
  rewrite H.
  discriminate.
Qed.
