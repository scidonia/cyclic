From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From stdpp Require Import gmap.
From Cyclic.Transform Require Import LLMOracle Supercompile LemmaProposer.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.

(** * Extraction of LLM-augmented supercompiler to OCaml
 
    Extract [LLM.residualise_jTy_llm] to an OCaml function.
    The [LLM.llm_generalise] Parameter is implemented by the OCaml shim in
    [bin/llm_oracle_impl.ml], which calls [llm_generalise.py --serve] via
    subprocess.
 
    The [LLMLemma.llm_propose_lemma] Parameter is also implemented there,
    calling [llm_generalise.py --serve-lemma].
 
    Build with:
        dune build bin/sc_llm.exe
    Run with:
        echo '<json>' | ./_build/default/bin/sc_llm.exe
*)

(** Provide OCaml implementations for stdpp types that Coq extracts opaquely. *)
Extract Constant stdpp.fin.fin => "int".
Extract Constant stdpp.fin.fin_0_inv => "assert false".

(** The LLM generalisation oracle: implemented by bin/llm_oracle_impl.ml *)
Extract Constant LLM.llm_generalise => "Llm_oracle_impl.llm_generalise".

(** The LLM lemma proposer: implemented by bin/llm_oracle_impl.ml *)
Extract Constant LLMLemma.llm_propose_lemma => "Llm_oracle_impl.llm_propose_lemma".

(** Extract both libraries to OCaml. *)
Extraction Library LLMOracle.
Extraction Library LemmaProposer.
