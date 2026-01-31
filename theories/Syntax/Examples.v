From Stdlib Require Import List Arith Utf8.
From Cyclic.Syntax Require Import StrictPos Term.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

(**
  Examples of indexed inductive families in the new Cyclic CIC system.
  
  This file demonstrates how to encode standard dependent types like:
  - Vec A n : length-indexed vectors
  - Eq A x y : propositional equality
  - Fin n : finite types
*)

Module Examples.

(** * Natural numbers (warm-up, non-indexed) *)

(**
  data Nat : Type where
    | zero : Nat
    | succ : Nat -> Nat
*)

Definition Nat_sig : ind_sig tm := {|
  ind_params := [];
  ind_indices := [];
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := [];
       ctor_rec_args := [];
       ctor_indices := []
    |};  (* zero *)
    {| ctor_param_tys := [];
       ctor_rec_args := [[]];  (* one rec arg at no specific index *)
       ctor_indices := []
    |}   (* succ *)
  ]
|}.

(** Assuming Nat is defined as inductive I=0, we can write: *)
Definition nat_ty : tm := tInd 0 [].
Definition zero : tm := tRoll 0 0 [].
Definition succ (n : tm) : tm := tRoll 0 1 [n].

(** * Length-indexed vectors *)

(**
  data Vec (A : Type) : Nat -> Type where
    | vnil : Vec A 0
    | vcons : forall (n : Nat), A -> Vec A n -> Vec A (S n)
    
  In our encoding:
  - ind_params = [Type]  (the element type A)
  - ind_indices = [Nat]  (the length n)
  - vnil ctor: result index [0]
  - vcons ctor: takes n:Nat, a:A, rec at index n, result index [S n]
*)

Definition Vec_sig : ind_sig tm := {|
  ind_params := [tSort 0];  (* A : Type *)
  ind_indices := [nat_ty];  (* n : Nat *)
  ind_level := 1;  (* Vec : Type -> Nat -> Type_1 *)
  ind_ctors := [
    {| ctor_param_tys := [];
       ctor_rec_args := [];
       ctor_indices := [zero]  (* vnil : Vec A 0 *)
    |};
    {| ctor_param_tys := [nat_ty; tVar 0];  (* n : Nat, a : A *)
       ctor_rec_args := [[tVar 1]];  (* rec arg at index n *)
       ctor_indices := [succ (tVar 1)]  (* result: Vec A (S n) *)
    |}
  ]
|}.

(** Assuming Vec is inductive I=1, Nat is I=0, we can write: *)
Definition vec_ty (A n : tm) : tm := tInd 1 [A; n].
Definition vnil (A : tm) : tm := tRoll 1 0 [].
Definition vcons (n A a v : tm) : tm := tRoll 1 1 [n; a; v].

(** Example: a vector [1; 2; 3] of natural numbers with length 3 *)
Definition vec_123 : tm :=
  vcons (succ (succ zero))  (* n = 2 *)
        nat_ty               (* A = Nat *)
        (succ zero)          (* 1 *)
        (vcons (succ zero)   (* n = 1 *)
               nat_ty
               (succ (succ zero))  (* 2 *)
               (vcons zero
                      nat_ty
                      (succ (succ (succ zero)))  (* 3 *)
                      (vnil nat_ty))).

(** * Propositional equality *)

(**
  data Eq (A : Type) (x : A) : A -> Type where
    | refl : Eq A x x
    
  In our encoding:
  - ind_params = [Type; A]  (the type A and left side x)
  - ind_indices = [A]  (the right side y)
  - refl ctor: no args, result index [x] (both sides equal)
*)

Definition Eq_sig : ind_sig tm := {|
  ind_params := [tSort 0; tVar 0];  (* A : Type, x : A *)
  ind_indices := [tVar 0];  (* y : A *)
  ind_level := 1;
  ind_ctors := [
    {| ctor_param_tys := [];
       ctor_rec_args := [];
       ctor_indices := [tVar 1]  (* refl : Eq A x x *)
    |}
  ]
|}.

(** Assuming Eq is inductive I=2: *)
Definition eq_ty (A x y : tm) : tm := tInd 2 [A; x; y].
Definition refl (A x : tm) : tm := tRoll 2 0 [].

(** * Finite types *)

(**
  data Fin : Nat -> Type where
    | fzero : forall n, Fin (S n)
    | fsucc : forall n, Fin n -> Fin (S n)
    
  In our encoding:
  - ind_params = []
  - ind_indices = [Nat]
  - fzero: takes n, result index [S n]
  - fsucc: takes n, rec at index n, result index [S n]
*)

Definition Fin_sig : ind_sig tm := {|
  ind_params := [];
  ind_indices := [nat_ty];
  ind_level := 1;
  ind_ctors := [
    {| ctor_param_tys := [nat_ty];  (* n : Nat *)
       ctor_rec_args := [];
       ctor_indices := [succ (tVar 0)]  (* fzero : Fin (S n) *)
    |};
    {| ctor_param_tys := [nat_ty];  (* n : Nat *)
       ctor_rec_args := [[tVar 0]];  (* rec arg at index n *)
       ctor_indices := [succ (tVar 0)]  (* fsucc : Fin (S n) *)
    |}
  ]
|}.

(** Assuming Fin is inductive I=3: *)
Definition fin_ty (n : tm) : tm := tInd 3 [n].
Definition fzero (n : tm) : tm := tRoll 3 0 [n].
Definition fsucc (n : tm) (f : tm) : tm := tRoll 3 1 [n; f].

(** Example: Fin 3 contains elements 0, 1, 2 *)
Definition fin_0 : tm := fzero (succ (succ zero)).  (* 0 : Fin 3 *)
Definition fin_1 : tm := fsucc (succ zero) (fzero zero).  (* 1 : Fin 3 *)
Definition fin_2 : tm := fsucc zero (fsucc zero (fzero zero)).  (* 2 : Fin 3 *)

(** * Using dependent case elimination *)

(**
  Example: head function for vectors
  
  head : forall A n, Vec A (S n) -> A
  head A n v = case v of
    | vnil => ...  (impossible branch, never selected)
    | vcons n' a v' => a
    
  The dependent motive here would be:
  C : Vec A ?len -> Type
  C = λ (v : Vec A ?len). A
  
  When the scrutinee is known to be (vcons n a v'), the motive becomes concrete.
*)

Definition head_body (A n v : tm) : tm :=
  tCase 1  (* Vec inductive *)
        v  (* scrutinee: v : Vec A (S n) *)
        A  (* motive: always return A (non-dependent motive in this case) *)
        [
          tVar 0;  (* vnil branch: impossible, but we need something *)
          tVar 1   (* vcons branch: return the second arg (the element) *)
        ].

Definition head : tm :=
  tLam (tSort 0)  (* A : Type *)
    (tLam nat_ty  (* n : Nat *)
      (tLam (vec_ty (tVar 1) (succ (tVar 0)))  (* v : Vec A (S n) *)
        (head_body (tVar 2) (tVar 1) (tVar 0)))).

End Examples.
