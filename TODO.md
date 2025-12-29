# TODO (Cyclic CoC)

This file tracks the current state + next steps so the work can be resumed
across opencode restarts.

## Current decisions

- Topic: cyclic proofs for a CoC-style dependent type theory.
- Build tool: `dune`.
- Use a library with finite maps/sets: `stdpp`.
- Preferred global condition formulation: ranking-based.
- Object language includes general recursion.
- Inductive types are via a general strictly-positive signature machinery (finitary W-type signatures; `Pos` is `Fin.t` of an arity).
- Operational semantics: call-by-name small-step (`theories/Semantics/Cbn.v`), with `case` applying branch to all constructor fields.
- Equality / program transformation correctness stays meta-theoretic for now.
- Canonicalization goal: define an operational procedure `Reduce` on proof objects and a behavioural relation `~` such that `p ~ Reduce(p)`.

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

- Decide whether successors are lists (ordered) vs sets/multisets (decision: keep `succ : V -> list V` for now; treat duplicates as allowed/irrelevant).
- Add basic path/cycle/SCC infra (done: `is_path`, `is_cycle`, `reachable_by_path`, inductive `reachable`, `mut_reachable`, `is_scc`, plus SCC lemmas in `theories/Graph/FiniteDigraph.v`).
- Decide whether graphs are total on `verts` or partial with domain proofs (decision: `succ` is a total function on `V`, but only constrained/meaningful on `verts` via `succ_closed`).

### 3) Progress condition (ranking / Büchi)

- Define edge annotations / trace positions needed for progress (started: `progress_edge` parameter + `has_progress_edge` and basic lemmas in `theories/Progress/Ranking.v`).
- Define ranking-based condition (started: `ranking_condition` record in `theories/Progress/Ranking.v`):
  - measure type, strict-decrease edge predicate, monotonicity.
- Optional: define Büchi/fairness acceptance and relate to ranking (decision: skip for now).

### 4) Proof equivalence (bisimulation)

- Define bisimulation over labelled proof graphs (started: `theories/Equiv/Bisimulation.v`).
- Prove it is an equivalence relation (pending: need symmetry/transitivity story across differing node types).
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
