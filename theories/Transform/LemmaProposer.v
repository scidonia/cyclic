From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile LemmaEnv.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

(** * LLM Lemma Proposer

    When the SC is stuck — neither AU, speculation, nor generalisation
    oracle succeeds — ask the LLM to propose an auxiliary lemma.

    The lemma is then validated by a sub-SC run ([LemmaEnv.validate_lemma]).
    If valid, it is added to [lemma_env] and the SC retried.

    This is the implementation of "cut introduction for the omega rule":
    the LLM proposes a cut formula (lemma statement), and the kernel
    validates it by proving it via the SC (i.e., cyclic induction).

    SOUNDNESS: the LLM is a [Parameter] — untrusted.  Only lemmas that
    pass [validate_lemma] are added.  The CIU theorem's validity is
    unaffected because lemmas are only used as rewrite rules, and every
    rewrite is justified by CIU equivalence proved by the sub-SC.
*)

Module LLMLemma.

  (** The LLM lemma proposal oracle.
      Given a stuck configuration and driving history, propose a lemma.
      Returns [None] if no useful lemma is found.

      In production this calls [llm_generalise.py --serve-lemma].
      At extraction it is replaced by the OCaml shim. *)
  Parameter llm_propose_lemma :
    SC.config ->              (* stuck configuration *)
    SC.config ->              (* companion from memo *)
    (* wrapper context — the f[·] pattern *)
    list (tm * tm) ->         (* driving history: (term, type) pairs *)
    option lemma.             (* proposed lemma, or None *)

  (** Validate a proposed lemma by running the sub-SC.
      Returns [true] iff the SC drives [lhs] to a residual equal to [rhs]. *)
  Definition validate_lemma
      (fuel_sc fuel_res : nat)
      (Σ : Ty.env) (l : lemma) (A : tm) : bool :=
    LemmaEnv.validate_lemma fuel_sc fuel_res Σ
      (lemma_lhs l) (lemma_rhs l) A.

  (** Check whether a proposed lemma is already in the environment
      (avoid duplicate proposals). *)
  Definition lemma_seen (l : lemma) (lemmas : lemma_env) : bool :=
    existsb
      (fun l' =>
         SC.tm_eqb (lemma_lhs l) (lemma_lhs l') &&
         SC.tm_eqb (lemma_rhs l) (lemma_rhs l'))
      lemmas.

  (** The full lemma proposal + validation loop.

      Given a stuck SC state, propose lemmas via the LLM and validate them.
      Returns the augmented lemma environment (possibly unchanged if no
      useful lemma was found or all proposals failed validation).

      This is the top-level "omega-rule cut introduction" step. *)
  Definition propose_and_validate_lemma
      (fuel_sc fuel_res : nat)
      (Σ : Ty.env)
      (stuck_j companion_j : SC.config)
      (history : list (tm * tm))
      (A : tm)
      (lemmas : lemma_env)
      : lemma_env :=
    match llm_propose_lemma stuck_j companion_j history with
    | None => lemmas (* LLM gave up *)
    | Some l =>
        if lemma_seen l lemmas then lemmas (* duplicate *)
        else if validate_lemma fuel_sc fuel_res Σ l A then
          l :: lemmas  (* accepted *)
        else lemmas    (* rejected *)
    end.

End LLMLemma.
