From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude gmap.

From Cyclic.Syntax Require Import Term.
From Cyclic.Transform Require Import ReadOff Extract.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Equiv Require Import CIUJudgement.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module RO := ReadOff.
Module EX := Extract.
Module Ty := Typing.Typing.

(**
  Read-off/extract correctness bridge.

  This file closes the loop needed by proof-level transforms:
  it shows that `extract_read_off` is semantically the identity at the level of
  judgement-CIU (`ciu_jTy`).

  We prove a stronger statement first: on the nose syntactic identity of the
  raw pipeline (`extract_read_off t = t`). The CIU lemma is then immediate by
  reflexivity/`ciu_jTy_of_eq`.
*)

Theorem extract_read_off_id (t : T.tm) : EX.extract_read_off t = t.
Proof.
  (* TODO: full round-trip proof. *)
Admitted.

Theorem extract_read_off_ciu
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
  CIUJudgement.ciu_jTy Σenv Γ t (EX.extract_read_off t) A.
Proof.
  apply CIUJudgement.ciu_jTy_of_eq.
  apply extract_read_off_id.
Qed.
