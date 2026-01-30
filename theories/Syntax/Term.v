From Stdlib Require Import List Arith Utf8.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos.

Import ListNotations.

Set Default Proof Using "Type".

Module Syntax.
  Inductive tm : Type :=
  | tVar (x : var)
  | tSort (i : nat)
  | tPi (A : tm) (B : {bind tm})
  | tLam (A : tm) (t : {bind tm})
  | tApp (t u : tm)
  | tFix (A : tm) (t : {bind tm})
  | tInd (I : nat) (args : list tm)                    (* I params indices *)
  | tRoll (I : nat) (c : nat) (args : list tm)         (* constructor with all args *)
  | tCase (I : nat) (scrut : tm) (C : {bind tm}) (brs : list tm).  (* dependent motive *)

  Definition branch (brs : list tm) (c : nat) : option tm :=
    nth_error brs c.

  Fixpoint size (t : tm) : nat :=
    match t with
    | tVar _ => 1
    | tSort _ => 1
    | tPi A B => 1 + size A + size B
    | tLam A t => 1 + size A + size t
    | tApp t u => 1 + size t + size u
    | tFix A t => 1 + size A + size t
    | tInd _ args =>
        1 + fold_right (fun u n => size u + n) 0 args
    | tRoll _ _ args =>
        1 + fold_right (fun u n => size u + n) 0 args
    | tCase _ scrut C brs =>
        1
        + size scrut
        + size C
        + fold_right (fun u n => size u + n) 0 brs
    end.

  Global Instance Ids_tm : Ids tm := tVar.
  Global Instance Rename_tm : Rename tm. derive. Defined.
  Global Instance Subst_tm : Subst tm. derive. Defined.
  Global Instance SubstLemmas_tm : SubstLemmas tm. derive. Qed.

  Definition ids : var -> tm :=
    @Autosubst_Classes.ids tm Ids_tm.

  Definition rename : (var -> var) -> tm -> tm :=
    @Autosubst_Classes.rename tm Rename_tm.

  Definition subst : (var -> tm) -> tm -> tm :=
    @Autosubst_Classes.subst tm Subst_tm.

  Definition up : (var -> tm) -> var -> tm :=
    @Autosubst_Classes.up tm Ids_tm Rename_tm.

  Definition subst0 (u : tm) (t : tm) : tm :=
    t.[u/].

  Definition shift_sub (d c : nat) : var -> var :=
    fun x => if x <? c then x else x + d.

  Definition shift (d c : nat) (t : tm) : tm :=
    rename (shift_sub d c) t.
End Syntax.
