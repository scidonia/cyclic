From Stdlib Require Import List Utf8.

From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Equiv Require Import CIUJudgement.
From Cyclic.Transform Require Import ReadOff Extract CaseCase ReadOffExtractCorrectness.

Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module RO := ReadOff.
Module EX := Extract.

(**
  Lifting case–case commute to the cyclic-proof universe.

  For now we treat the cyclic proof object as the raw read-off graph (`builder` + root).

  - The transformation is implemented by `extract` -> term-level commute -> `read_off_raw`.
  - The equivalence notion is the judgement-level CIU relation on extracted terms.

  This file is structured so that the only missing bridge is the read-off/extract
  correctness lemma stated as `extract_read_off_ciu` below.
*)

Definition raw_proof : Type := nat * RO.builder.

Definition extract_raw (p : raw_proof) : tm :=
  EX.extract (snd p) (fst p).

Definition case_case_transform (Σenv : Ty.env) (p : raw_proof) : raw_proof :=
  let '(root, b) := p in
  let '(root', b') := CaseCase.commute_case_case_builder Σenv b root in
  (root', b').

Definition proof_equiv_raw (Σenv : Ty.env) (Γ : Ty.ctx) (t u A : tm) : Prop :=
  CIUJudgement.ciu_jTy Σenv Γ t u A.

(**
  Bridge needed to relate `extract (read_off_raw t)` back to `t`.

  This is exactly the (typed) read-off/extract correctness theorem for the raw pipeline.
  It is expected to be proved as part of the isomorphism development.
*)
Theorem case_case_transform_preserves_equiv
    (Σenv : Ty.env) (Γ : Ty.ctx) (p : raw_proof) (A : tm) :
  Ty.has_type Σenv Γ (extract_raw p) A ->
  CIUJudgement.ciu_jTy Σenv Γ (extract_raw p) (extract_raw (case_case_transform Σenv p)) A.
Proof.
Admitted.
