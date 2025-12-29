From Stdlib Require Import List Utf8 Vectors.Fin.

Import ListNotations.

Set Default Proof Using "Type".

(* Strictly-positive inductive signatures, as finitely-branching containers.

   We parameterize the signature by a type of "object-level types" `Ty`.
   This avoids a dependency from signatures to the term syntax.

   A signature consists of:
   - a type of constructor shapes `Shape`
   - for each shape `s`, a finite list of non-recursive parameter types
     (encoded by an arity and a type assignment `param_ty`)
   - for each shape `s`, a finite number of recursive fields (arity)

   Recursive positions are `Fin.t (arity s)`.
*)

Record ind_sig (Ty : Type) : Type := {
  Shape : Type;
  (* Number of non-recursive constructor parameters (finitary). *)
  param_arity : Shape -> nat;
  (* Type of each non-recursive parameter. *)
  param_ty : forall s : Shape, Fin.t (param_arity s) -> Ty;
  (* Number of recursive constructor fields (finitary). *)
  arity : Shape -> nat;
}.

Arguments Shape {_} _.
Arguments param_arity {_} _ _.
Arguments param_ty {_} _ _ _.
Arguments arity {_} _ _.

Definition ParamPos {Ty : Type} (Σ : ind_sig Ty) (s : Shape Σ) : Type :=
  Fin.t (param_arity Σ s).

Definition Pos {Ty : Type} (Σ : ind_sig Ty) (s : Shape Σ) : Type :=
  Fin.t (arity Σ s).

Fixpoint enumFin (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n' => Fin.F1 :: map Fin.FS (enumFin n')
  end.

(* A basic W-type carrier for such signatures (non-indexed). *)
Inductive ind_carrier {Ty : Type} (Σ : ind_sig Ty) : Type :=
| sup : forall s : Shape Σ, (Pos Σ s -> ind_carrier Σ) -> ind_carrier Σ.

Arguments sup {_ _} _ _.

Definition ind_zero (Ty : Type) : ind_sig Ty :=
  {| Shape := Empty_set
   ; param_arity := fun e => match e with end
   ; param_ty := fun e => match e with end
   ; arity := fun e => match e with end |}.

Definition ind_const (Ty : Type) (A : Type) : ind_sig Ty :=
  {| Shape := A
   ; param_arity := fun _ => 0
   ; param_ty := fun _ i => match i with end
   ; arity := fun _ => 0 |}.

Definition ind_sum {Ty : Type} (Σ1 Σ2 : ind_sig Ty) : ind_sig Ty :=
  {| Shape := (Shape Σ1 + Shape Σ2)%type
   ; param_arity := fun s =>
       match s with
       | inl s1 => param_arity Σ1 s1
       | inr s2 => param_arity Σ2 s2
       end
   ; param_ty := fun s =>
       match s as s0
       return Fin.t (match s0 with inl s1 => param_arity Σ1 s1 | inr s2 => param_arity Σ2 s2 end) -> Ty with
       | inl s1 => fun i => param_ty Σ1 s1 i
       | inr s2 => fun i => param_ty Σ2 s2 i
       end
   ; arity := fun s =>
       match s with
       | inl s1 => arity Σ1 s1
       | inr s2 => arity Σ2 s2
       end |}.
