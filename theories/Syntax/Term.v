From Stdlib Require Import List Utf8.

From Cyclic.Syntax Require Import StrictPos.

Import StrictPos.
Import ListNotations.

Set Default Proof Using "Type".

(* Raw (untyped) syntax for a CoC-style dependent calculus with general recursion
   and inductive data (given by strictly-positive signatures).

   This is intentionally lightweight: typing, conversion, and operational
   semantics will live in separate files.

   We use de Bruijn indices for binders.
*)

Module Syntax.
  Inductive ty : Type :=
  | TyU
  | TyPi (A : ty) (B : ty) (* B lives in extended context *)
  | TyInd (Σ : ind_sig).

  Inductive tm : Type :=
  | tVar (x : nat)
  | tLam (A : ty) (t : tm)
  | tApp (t u : tm)
  | tFix (A : ty) (t : tm) (* t is in extended context, binds the recursive name *)
  | tRoll (Σ : ind_sig) (s : Shape Σ)
      (params : ParamPos Σ s -> tm)
      (k : Pos Σ s -> tm)
  | tCase (Σ : ind_sig) (scrut : tm) (C : ty) (br : Shape Σ -> tm).
End Syntax.
