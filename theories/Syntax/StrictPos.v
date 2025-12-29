From Stdlib Require Import List Utf8 Vectors.Fin.

Import ListNotations.

Set Default Proof Using "Type".

(* Strictly-positive inductive signatures, as finitely-branching containers.

   A signature consists of:
   - a type of constructor shapes `Shape`
   - for each shape `s`, a *finite* arity `arity s : nat`

   Recursive positions are then `Fin.t (arity s)`. This finitary choice is what
   lets us give an operational semantics for pattern matching that can pass all
   constructor fields to a branch.

   Example: `List A` can be encoded with
   - Shape := unit + A
   - arity (inl tt) := 0
   - arity (inr a) := 1
*)

Record ind_sig : Type := {
  Shape : Type;
  (* Number of non-recursive constructor parameters (finitary). *)
  param_arity : Shape -> nat;
  (* Number of recursive constructor fields (finitary). *)
  arity : Shape -> nat;
}.

Definition ParamPos (Σ : ind_sig) (s : Shape Σ) : Type :=
  Fin.t (param_arity Σ s).

Definition Pos (Σ : ind_sig) (s : Shape Σ) : Type :=
  Fin.t (arity Σ s).

Inductive ind_carrier (Σ : ind_sig) : Type :=
| sup : forall s : Shape Σ, (Pos Σ s -> ind_carrier Σ) -> ind_carrier Σ.

Arguments sup {_} _ _.

Definition ind_zero : ind_sig :=
  {| Shape := Empty_set
   ; param_arity := fun e => match e with end
   ; arity := fun e => match e with end |}.

Definition ind_const (A : Type) : ind_sig :=
  {| Shape := A
   ; param_arity := fun _ => 0
   ; arity := fun _ => 0 |}.

Definition ind_sum (Σ1 Σ2 : ind_sig) : ind_sig :=
  {| Shape := (Shape Σ1 + Shape Σ2)%type
   ; param_arity := fun s =>
       match s with
       | inl s1 => param_arity Σ1 s1
       | inr s2 => param_arity Σ2 s2
       end
   ; arity := fun s =>
       match s with
       | inl s1 => arity Σ1 s1
       | inr s2 => arity Σ2 s2
       end |}.

Definition ind_prod (Σ1 Σ2 : ind_sig) : ind_sig :=
  {| Shape := (Shape Σ1 * Shape Σ2)%type
   ; param_arity := fun s =>
       match s with
       | (s1, s2) => param_arity Σ1 s1 + param_arity Σ2 s2
       end
   ; arity := fun s =>
       match s with
       | (s1, s2) => arity Σ1 s1 + arity Σ2 s2
       end |}.
