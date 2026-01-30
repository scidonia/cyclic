From Stdlib Require Import List Arith Utf8.

Import ListNotations.

Set Default Proof Using "Type".

(* Finitary strictly-positive inductive signatures for indexed inductive families.

   This supports CIC-style indexed inductive types (e.g., Vec A n, Eq A x y, Fin n).
   
   An inductive signature consists of:
   - Uniform parameters (e.g., A in Vec A n)
   - Indices (e.g., n in Vec A n; x and y in Eq A x y)
   - A universe level
   - A list of constructors

   Each constructor has:
   - Non-recursive argument types
   - Recursive argument specifications: for each rec field, the list of indices
     at which that recursive occurrence happens
   - Result indices: the indices at which this constructor produces a value
     (e.g., vnil : Vec A 0 has result index [0]; vcons : Vec A n -> Vec A (S n) 
      has result index [S n])

   This representation is consumed by a typing judgement parameterized over
   a global environment of such signatures.
*)

Record ctor_sig (Ty : Type) : Type := {
  ctor_param_tys : list Ty;        (* non-recursive arguments *)
  ctor_rec_args : list (list Ty);  (* for each rec field: indices at that occurrence *)
  ctor_indices : list Ty           (* constructor result indices *)
}.

Arguments ctor_param_tys {_} _.
Arguments ctor_rec_args {_} _.
Arguments ctor_indices {_} _.

Record ind_sig (Ty : Type) : Type := {
  ind_params : list Ty;            (* uniform parameters *)
  ind_indices : list Ty;           (* index types (may depend on params) *)
  ind_level : nat;                 (* universe level *)
  ind_ctors : list (ctor_sig Ty)   (* constructors *)
}.

Arguments ind_params {_} _.
Arguments ind_indices {_} _.
Arguments ind_level {_} _.
Arguments ind_ctors {_} _.

(* Helper functions for arities *)

Definition ctor_param_arity {Ty : Type} (c : ctor_sig Ty) : nat :=
  length (ctor_param_tys c).

Definition ctor_rec_arity {Ty : Type} (c : ctor_sig Ty) : nat :=
  length (ctor_rec_args c).

Definition ctor_arity {Ty : Type} (c : ctor_sig Ty) : nat :=
  ctor_param_arity c + ctor_rec_arity c.

Definition ind_param_arity {Ty : Type} (Σ : ind_sig Ty) : nat :=
  length (ind_params Σ).

Definition ind_index_arity {Ty : Type} (Σ : ind_sig Ty) : nat :=
  length (ind_indices Σ).

Definition ind_arity {Ty : Type} (Σ : ind_sig Ty) : nat :=
  ind_param_arity Σ + ind_index_arity Σ.

(* Lookup functions *)

Definition lookup {A : Type} (xs : list A) (n : nat) : option A :=
  nth_error xs n.

Definition lookup_ind {Ty : Type} (Σenv : list (ind_sig Ty)) (I : nat) : option (ind_sig Ty) :=
  lookup Σenv I.

Definition lookup_ctor {Ty : Type} (Σ : ind_sig Ty) (c : nat) : option (ctor_sig Ty) :=
  lookup (ind_ctors Σ) c.

Lemma lookup_ctor_lt {Ty : Type} (Σ : ind_sig Ty) (c : nat) (ctor : ctor_sig Ty) :
  lookup_ctor Σ c = Some ctor -> c < length (ind_ctors Σ).
Proof.
  unfold lookup_ctor, lookup.
  intro H.
  apply nth_error_Some.
  rewrite H.
  discriminate.
Qed.
