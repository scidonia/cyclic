From Stdlib Require Import List Utf8.
From stdpp Require Import prelude countable.

From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Equiv Require Import Bisimulation.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module Ty := Typing.Typing.

(**
  Read-off / extraction specification

  This file specifies (but does not yet implement) the first major transform:

  - `read_off` turns a CIC-style term (with `fix`) into a cyclic pre-proof graph.
  - `extract` turns such a cyclic pre-proof graph back into a CIC term.

  Design intent:

  - During read-off, *calls/applications of fixed points* are replaced by
    explicit typed substitutions and back-links in the proof graph.
  - All other term constructors are represented purely by judgements and proof
    structure, i.e. we do not store the original term syntax inside nodes.

  - During extraction, we traverse the graph from the root and synthesize
    a `fix` binder for each back-link, then re-use that binder at each
    occurrence of the back-link. This requires tracking which nodes are
    designated back-links during traversal.

  Deliverable (eventually): the two transformations form an isomorphism
  (up to an appropriate proof-graph equivalence).

  NOTE: This is written as a `Module Type` so it introduces no axioms.
  An implementation module will later provide the constructions and proofs.
*)

Module Type READOFF_SPEC.
  (** Judgement language used to label the cyclic proof graph.

      This is intentionally *term-less* except for back-link payloads.

      The idea is:
      - the proof graph structure encodes the shape of the term
      - back-links carry explicit typed substitutions (arguments)
  *)
  Parameter judgement : Type.

  (** Rule relation for cyclic pre-proofs produced by read-off. *)
  Parameter rule : Ty.env -> judgement -> list judgement -> Prop.

  (** Back-link payload extracted from a judgement, if it is a back-link.

      Intended meaning:
      - `Δ` is the environment/context at the back-link site
      - `σ` is the *typed substitution* representing the arguments
      - `Γ` is the "target" context / schematic context for the back-link

      The exact choice of payload is part of the upcoming design.
  *)
  Parameter backlink_payload : Type.
  Parameter is_backlink : judgement -> option backlink_payload.

  (** A convenient concrete vertex type for generated graphs. *)
  Definition V : Type := nat.


  Definition preproof (Σenv : Ty.env) : Type :=
    @Preproof.preproof judgement (rule Σenv) V _ _.

  Definition rooted_preproof (Σenv : Ty.env) : Type :=
    @Preproof.rooted_preproof judgement (rule Σenv) V _ _.

  (** Read off a term into a rooted cyclic pre-proof.

      The input is a CIC term goal: `Γ ⊢ t : A`.

      The output graph must represent:
      - all term constructors via proof structure
      - all fixed-point call sites via explicit back-link judgements
        containing typed substitutions
  *)
  Parameter read_off :
    forall (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm), rooted_preproof Σenv.

  (** Extract a CIC term goal from a rooted cyclic pre-proof.

      Since the cyclic proof graph is (mostly) term-less, extraction must:
      - traverse the graph from the root
      - detect back-link nodes using `is_backlink`
      - introduce a `fix` binder for each back-link (once)
      - re-use that binder at subsequent occurrences
  *)
  Parameter extract_goal :
    forall (Σenv : Ty.env), rooted_preproof Σenv -> Ty.ctx * (T.tm * T.tm).

  Parameter extract :
    forall (Σenv : Ty.env), rooted_preproof Σenv -> T.tm.

  (** Graph equivalence used for the isomorphism law.

      We expect read-off/extract to round-trip up to bisimulation (or a related
      notion). The implementation may strengthen/weaken this as needed.
  *)
  Parameter proof_equiv :
    forall (Σenv : Ty.env),
      rooted_preproof Σenv -> rooted_preproof Σenv -> Prop.

  (** Isomorphism laws (to be proved by the implementation). *)

  Parameter extract_read_off_id :
    forall (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm),
      extract Σenv (read_off Σenv Γ t A) = t.

  Parameter read_off_extract_iso :
    forall (Σenv : Ty.env) (p : rooted_preproof Σenv),
      let '(Γ,(t,A)) := extract_goal Σenv p in
      proof_equiv Σenv (read_off Σenv Γ t A) p.
End READOFF_SPEC.
