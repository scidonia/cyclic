# TODO (Cyclic CoC)

This file tracks the current state + next steps so the work can be resumed
across opencode restarts.

## Current decisions

- Topic: cyclic proofs for a CoC-style dependent type theory.
- Build tool: `dune`.
- Use a library with finite maps/sets: `stdpp`.
- Preferred global condition formulation: ranking-based (with Büchi/fairness view
  as a secondary/equivalent characterization).

## Toolchain status (important)

This repo briefly went through multiple Rocq/Coq versions during `stdpp` setup.
If you see errors like “bad version number … expected …”, restart your Coq LSP
and ensure it uses the same `opam` switch as the terminal.

At the moment (in this container), `stdpp` available on opam constrains Coq/Rocq
< 9.1, so the consistent state uses Rocq/Coq 9.0.x.

Useful checks:
- `which coqc`
- `coqc --version`
- `opam list --installed | rg 'rocq|coq|stdpp|coq-lsp'`

## Files created so far

- `README.md` (project overview, tooling notes, opam sketch)
- `cyclic_coc_sketch.md` (your design sketch)

Initial Coq “machinery” modules:
- `theories/Graph/FiniteDigraph.v`
  - finite directed graph structure over a `stdpp`-finite node type
  - `verts : gset V`, `succ : V -> list V`, closure proof
  - basic `edge` and `out_neighbours`
- `theories/Preproof/Preproof.v`
  - pre-proofs: graph + judgement labels + local rule correctness
  - rooted pre-proofs

Note: these `.v` files compile when invoked directly with:
- `coqc -Q theories Cyclic theories/Graph/FiniteDigraph.v`
- `coqc -Q theories Cyclic theories/Preproof/Preproof.v`

`dune` integration is now added.

- Added `dune-project`.
- Added `theories/dune` with a `(coq.theory ...)` stanza.
- `dune build` compiles `FiniteDigraph.v` and `Preproof.v`.
- Current logical root name is `Cyclic`.

## Next steps (in order)

### 2) Polish graph & pre-proof interfaces

- Decide whether successors are lists (ordered) vs sets/multisets.
- Add basic path/cycle definitions (done: `is_path`, `is_cycle` in `theories/Graph/FiniteDigraph.v`).
- Decide whether graphs are total on `verts` or partial with domain proofs.

### 3) Progress condition (ranking / Büchi)

- Define edge annotations / trace positions needed for progress.
- Define ranking-based condition:
  - measure type, strict-decrease edge predicate, monotonicity.
- Optional: define Büchi/fairness acceptance and relate to ranking.

### 4) Proof equivalence (bisimulation)

- Define bisimulation over labelled proof graphs.
- Prove it is an equivalence relation.
- Prove it respects unfolding/interpretation (once semantics exists).

### 5) Fold/refold + canonicalization

- Define fold/refold operations on pre-proofs/proofs.
- Prove preservation of:
  - local correctness
  - progress acceptance
  - bisimulation class
- Begin SCC-based “reasonably canonical” normal form design.

## Open design questions

- What counts as a “progress event” for CoC-style cyclic equality?
  - which rule steps are designated progress
  - what strictly decreases
  - do we carry a witness (ranking) as data or require existence

- What library strategy for graph algorithms?
  - implement SCC/reachability over `stdpp` containers vs add another library
