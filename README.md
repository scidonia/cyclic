# Cyclic CoC (work in progress)

This repository explores **cyclic proofs** for a dependent type theory close to the
Calculus of Constructions (CoC).

The guiding slogan (from `cyclic_coc_sketch.md`) is:

> Canonical cyclic proofs are intensional representatives whose equality soundly
> approximates extensional program equivalence.

In this approach, proof objects are **finite graphs** (not trees). Cycles are
allowed locally, and soundness is recovered by a **global progress condition**
(e.g. via rankings / Büchi-style acceptance).

## Scope (initial milestone)

- A core dependent λ-calculus with Π-types (no universes initially).
- An inductive typing judgement `Γ ⊢ t : A`.
- A cyclic/intensional equality judgement `Γ ⊢ t ≈ u : A`.
- Graph-shaped proof objects with:
  - **local correctness** (every node is justified by a rule instance)
  - **global progress** (no cycle can “stall”)
- A notion of proof equivalence via **bisimulation**.
- Fold/refold transformations and an attempt at “reasonably canonical” cyclic
  representatives (canonicalization w.r.t. cycles).

Non-goals initially:
- Full CoC universes/cumulativity (deferred).
- Fully automated canonicalization (we aim for a stable, usable notion first).

## Quick orientation

The design sketch lives in:
- `cyclic_coc_sketch.md`

That document is the source of truth for the high-level architecture; `README.md`
records the intended mechanization and milestones.

## Judgements

We work with:
- Contexts `Γ`
- Terms `t, u`
- Types `A, B`

Judgements include (initially):

- Typing (inductive):
  - `Γ ⊢ t : A`

- Equality / conversion (cyclic):
  - `Γ ⊢ t ≈ u : A`

Important: `≈` is not standard CoC judgmental equality. It is a cyclicly
justified, **intensional** equality relation on representatives.

## Rules and local correctness

Rules are treated abstractly as a relation of the form:

```text
Rule : Judgement → list Judgement → Prop
```

A **pre-proof** is a finite directed graph where:

- nodes are a finite type (e.g. `Fin n`)
- each node has a judgement label `label : node → Judgement`
- edges go from a conclusion node to its premise nodes `succ : node → list node`

Local correctness is the condition:

```text
Rule (label n) (map label (succ n))
```

for each node `n`.

## Global soundness: progress on cycles

Local correctness alone does not prevent unsound cyclic “proofs”. A pre-proof
becomes a **cyclic proof** only after it satisfies a **global progress
condition** ensuring that cycles make progress.

### Two equivalent views (we expect to relate them)

- **Ranking-based** (preferred for mechanization):
  - attach a well-founded measure to nodes / trace positions
  - require every directed cycle to contain a strict descent, and other steps to
    be non-increasing

- **Büchi / fairness-based** (classical cyclic proof theory view):
  - define “progress events” on edges/rule-steps
  - require every infinite path to see progress events infinitely often

A core engineering problem of the project is the *machinery* for representing
finite proof graphs plus the additional structure needed to check/transport a
progress witness.

## Semantics and soundness goal

We aim to define a semantic interpretation (e.g. PER/logical relation style)

```text
⟦ label(root) ⟧ : Prop
```

and prove a soundness theorem of the shape:

```text
PreProof + LocalCorrectness + GlobalProgress → SemanticValidity
```

This is the cyclic-proof slogan:

> finite object + global condition → sound infinite meaning

## Proof equivalence: bisimulation

We want an explicit notion of equivalence of cyclic proofs suitable for
“intensional representatives”.

Planned approach:
- define a **bisimulation** relation over proof graphs (and possibly over
  distinguished roots)
- require it to respect judgement labels and successor structure
- ensure it interacts well with the global progress condition

Target properties:
- bisimulation is an equivalence relation
- bisimilar proofs have the same unfolding/semantic meaning
- bisimulation is preserved by fold/refold transformations

## Fold / refold transformations and canonicalization

We want to justify proof refactorings that change cyclic structure without
changing meaning.

- **Folding**: identify repeated sub-derivations and add back-links (create cycles).
- **Refolding**: restructure cycles while preserving local steps and progress.

The longer-term goal is to compute (or at least define) **reasonably canonical
representatives** by normalizing graph structure w.r.t. cycles (e.g. SCC-based
normal forms), and to justify that canonicalization preserves the induced
bisimulation/equivalence class.

## Tooling

- Build system: `dune`
- Proof assistant: developed against `coqc --version` = “The Rocq Prover 9.1.0”
  (the Coq/Rocq installed in this environment)

### Libraries

For finite sets and maps, the baseline plan is to use:
- `stdpp` (Iris project): provides `gmap`, `gset`, finite-map/set reasoning, and
  a good foundation for representing finite graphs (e.g. as adjacency maps).

If we later want dedicated graph algorithms (SCC, reachability, etc.), we can
either implement them over `stdpp` containers or add a separate graph library.

## Build (dune)

Once the Coq sources and `dune` files exist, typical commands will be:

- Build everything: `dune build`
- Clean: `dune clean`

### Dependencies (opam sketch)

This is a non-binding sketch for setting up dependencies with `opam`. Package
names differ slightly between “Coq” and “Rocq” distributions, so treat this as a
starting point and adjust based on `opam search`.

Typical ingredients:
- the prover (`rocq-prover` / `coq`), matching the version you have installed
- `stdpp` (`rocq-stdpp` / `coq-stdpp`)

Example (illustrative):

```sh
# Create a local switch (optional)
opam switch create . ocaml-base-compiler.4.14.1

# Install the prover + stdpp (package names may vary)
opam install rocq-prover rocq-stdpp

# Or, on older Coq package naming:
# opam install coq coq-stdpp
```

If in doubt:
- `opam search stdpp`
- `opam show rocq-prover` (or `opam show coq`)

Dependency installation will be made precise once the repository has a
`dune-project` and package metadata.

## Planned layout

Target directory layout (subject to change):

- `theories/Graph/` finite graphs, paths, cycles, SCCs
- `theories/Judgement/` syntax of terms/types/contexts and judgements
- `theories/Rules/` rule schemas and instantiation
- `theories/Preproof/` pre-proofs and local correctness
- `theories/Progress/` ranking condition and/or Büchi acceptance
- `theories/CyclicProof/` cyclic proof definition + soundness interface
- `theories/Equiv/` bisimulation and its properties
- `theories/Transform/` folding/refolding + preservation theorems
- `theories/Examples/` small worked cyclic proofs

## Milestones (research checklist)

- Define core syntax and inductive typing.
- Define cyclic equality rules as graph-labelled inference.
- Implement finite proof graphs and local correctness.
- Specify progress annotations (trace positions / edge kinds).
- Relate ranking-based progress and Büchi/fairness acceptance.
- Define bisimulation over proofs.
- Specify fold/refold transformations; prove they preserve bisimulation and progress.
- Define a canonicalization strategy w.r.t. cycles; prove invariance.

## Next decision: what counts as “progress”?

To make the development concrete, we still need the precise notion of a
“progress event” for CoC-style cyclic equality. Concretely:

- what must strictly decrease (a syntactic measure? trace position? redex depth?)
- which rule-steps are designated as progress steps
- whether the proof carries an explicit witness (ranking function / progress tags)
  or we only require existence
