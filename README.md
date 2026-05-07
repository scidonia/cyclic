# Cyclic: Supercompilation as Cyclic Proof Search

Mechanised in Rocq with 0 axioms and 0 admitted lemmas.

## Papers

- **`papers/esop-2027/`** — *"Supercompilation as Cyclic Proof Search for the Calculus of Constructions"* (ESOP 2027 submission). Establishes the proof-theoretic foundation: driving = cut elimination, splitting = ∨-left, folding = cyclic backlink, trace condition = global progress. Four-claim pipeline (pre-proof → cyclic proof → CIU → validation) mechanised in Rocq.

- **`papers/hls-2027/`** — *"Program Transformation as Theorem Proving: LLMs as Untrusted Proof Oracles"*. Extends the foundation with an LLM oracle for generalisation (untrusted, kernel-validated), an ω-rule for lemma synthesis (LLM proposes, sub-SC proves, main SC uses), and dependent-type branch elimination. 70+ theorems, 0 admitted.

## Build

Requires Rocq 9.x and stdpp.

```sh
dune build
```

## Directory structure

| Directory | Purpose |
|---|---|
| `theories/Syntax/` | Term language, strict positivity, example inductives (Nat, List, Vec, Maybe, Expr, Value) |
| `theories/Judgement/` | Typing and sequent typing |
| `theories/Semantics/` | Call-by-name operational semantics |
| `theories/Graph/` | Finite directed graphs, SCCs |
| `theories/Preproof/` | Pre-proof construction |
| `theories/CyclicProof/` | Cyclic proof system and ranking |
| `theories/Progress/` | Ranking, homeomorphic embedding, pattern unification |
| `theories/Transform/` | **Supercompiler, LLM oracle, omega rule, lemma environment, dependent pruning** |
| `theories/Equiv/` | CIU equivalence, bisimulation, CIU for judgements |

## Key theorems

| Theorem | File | Statement |
|---|---|---|
| `supercompile_ciu_soundness_untyped` | `SupercompilationCorrespondence.v` | CIU equivalence of SC residual |
| `trace_condition_ok_no_nonprogress_cycle` | `SupercompileTraceCheckSound.v` | Trace condition ensures well-foundedness |
| `best_generalize_llm` | `LLMOracle.v` | 3-layer generalisation: AU → LLM oracle → LLM lemma |
| `lemma_driven_residualise` | `OmegaRule.v` | Lemma-driven SC with rewrite rules |
| `plus_commutativity` | `Commutativity.v` | Commutativity of addition (omega rule) |
| `pruning_enables_equality` | `DependentPruning.v` | Dead-branch elimination via type indices |
| `filter_odd_any_even_is_false` | `ParityLemma.v` | Parity-filter interaction |
| `lemma_rev_acc_append_distrib_validated` | `LLMLemmaInAction.v` | Sub-SC validates LLM-proposed lemma |
| `cast_roundtrip_omega` | `GradualCast.v` | Gradual cast safety (omega rule) |
| `compiler_main_with_lemma` | `CompilerCorrectness.v` | Compiler soundness (omega rule) |

## Contact

Gavin Mendel-Gleason — gavin@scidonia.ai
