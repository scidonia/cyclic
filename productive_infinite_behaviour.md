# Productive Infinite Behaviour (No Bottom): What We’d Need

This note sketches what it would take to extend the current development so we can
represent **infinite behaviours** (e.g. streams / reactive programs) in a way that
is **productive** (always able to reveal the next observable step) and does **not
rely on bottom**.

It also explains how this interacts with our current cyclic-proof machinery:
`Preproof`, `CyclicProof`, `Ranking`, and `Bisimulation`.

## Current state (what we already have)

- A *raw* term language with general recursion (`tFix`) and inductives (`tInd`, `tRoll`, `tCase`) in `theories/Syntax/Term.v`.
- A call-by-name weak-head step relation `step` and WHNF notion in `theories/Semantics/Cbn.v`.
- A generic notion of proof graphs (“preproofs”) in `theories/Preproof/Preproof.v`.
- A concrete judgement layer that can express typing, equality, and explicit substitutions in `theories/Judgement/Typing.v`.
- A generic wrapper for “cyclic proof = preproof + progress witness” in `theories/CyclicProof/CyclicProof.v`.
- A ranking-style progress condition template (well-founded decrease along designated progress edges) in `theories/Progress/Ranking.v`.

### Why this isn’t enough for “productive infinite behaviour”

General recursion (`tFix`) allows divergence. Divergence is *bottom-like* in the
operational semantics (`diverges` in `theories/Semantics/Cbn.v`).

If we want **infinite behaviour without bottom**, we need to ensure that any
infinite computation is **productive**: it keeps producing observable structure
(constructors / outputs) and never gets stuck in unproductive looping.

In proof-theoretic terms: ranking-based cyclic soundness is naturally an
**inductive**/well-founded argument. Productivity is naturally
**coinductive**/fairness-like.

## What “productive infinite behaviour” means (operationally)

There are two common operational characterizations, depending on the observation
we care about:

1. **Constructor productivity (data streams)**
   - A term of coinductive type can always reduce (in finite time) to reveal a
     constructor at the head.
   - Repeatedly forcing/unfolding continues to reveal constructors.

2. **Step productivity (reactive/process semantics)**
   - A term can always take a (labelled) transition producing an observable
     action.
   - Infinite behaviours are infinite labelled traces.

In either case, “no bottom” means we reject definitions whose infinite behaviour
comes from *divergent internal computation* rather than *guarded unfolding*.

## What needs to be added (design options)

### Option A: Add **coinductive types** + **guarded corecursion** (Coq-style)

Add new syntax/typing constructs:

- A coinductive type former / signature (dual to `StrictPos` inductives)
  - Either extend `theories/Syntax/StrictPos.v` with coinductive signatures
    (greatest fixpoints) OR introduce a parallel “coinductive signature” module.
- A corecursive term former (`cofix` / `tCoFix`) producing a coinductive value.
- An explicit unfolding operation (often implicit in reduction) that reveals one
  constructor layer of a coinductive value.

Add a **guardedness/productivity check** at the typing level:

- Ensure corecursive calls are guarded by a constructor (or by a
  coinductive-destructor discipline).
- This check is syntactic (like Coq’s guardedness) or semantic (like sized
  types / clocked types).

Operational semantics changes:

- Extend `theories/Semantics/Cbn.v` with reduction rules for `cofix`:
  - Typically: `cofix f := t` unfolds to `t[cofix f := t / f]` *only when forced*
    (so unfolding is controlled and corresponds to observation).
- Introduce an explicit notion of **observation/forcing** for coinductive values
  (e.g. a destructor or `case`-like eliminator for coinductives).

Why this avoids bottom:

- Productivity ensures that each observation triggers only a finite amount of
  computation before a constructor is produced.
- Non-productive definitions are rejected, so divergence is not allowed at
  coinductive types.

### Option B: Keep types as-is, but add a **process/trace semantics** and require productivity there

Instead of extending the type theory with coinductives, define an explicit
semantic notion of observable steps:

- Define a labelled transition system (LTS) for some subset of terms.
- Define productivity as: for any state, there exists a finite reduction to an
  observable action/constructor.

This is sometimes easier if “infinite behaviour” is about interaction rather
than infinite data.

## How cyclic proofs relate (and what must change)

### Ranking witnesses are inductive; productivity is coinductive

Our current progress template (`theories/Progress/Ranking.v`) uses a
well-founded order `ltM_wf`. This is ideal for showing:

- “cycles are OK because something decreases”

That is a good fit for termination / normalization-like arguments.

But productivity arguments typically look like:

- “on any infinite path, some good event happens infinitely often”

This is **fairness / Büchi / parity acceptance**, not well-founded descent.

### What we need to add on the proof side

We can keep the existing `CyclicProof` packaging (it’s parametric in a witness),
but we need a *different witness kind* for coinductive/productive reasoning.

Concretely:

1. Keep `theories/CyclicProof/CyclicProof.v` as the common interface.
2. Add a new progress witness module (parallel to `Ranking.v`), for example:
   - `theories/Progress/Buchi.v` or `theories/Progress/Parity.v`

A Büchi-style witness would:

- designate a set of “good edges” (or good nodes / rule instances)
- require that every infinite path visits good edges infinitely often

For finite graphs, this can be checked via SCC reasoning:

- every reachable SCC contains a good edge (or a good node)

This SCC characterization is often the most extraction-friendly: it yields a
finite certificate about SCCs instead of quantifying over infinite paths.

A parity-style witness generalizes Büchi and is closer to mixing induction +
coinduction in one proof object.

### How this connects to *current* equality rules

In `theories/Judgement/Typing.v`, equality `jEq` currently includes:

- reflexive/sym/trans rules
- a computational step rule using `Semantics.Cbn.step`
- substitution transport

For productivity-style reasoning, we’d likely want to distinguish (as data in the
rule/witness layer) which edges correspond to:

- “observation steps” (constructor revealed / action emitted)
- “administrative steps” (symmetry/transitivity/substitution transport)

Then:

- the progress witness should demand that observation steps occur fairly/often
  on cycles (Büchi/parity), not that some measure decreases.

This suggests refactoring the progress-edge predicate to be driven by *rule
instances*, not just arbitrary edges.

## What would be necessary for extraction

If we want to extract productive programs to OCaml/Haskell:

- For Option A (coinductives + cofix): extraction naturally targets lazy values
  or explicit thunks.
- We need the productivity witness to be **proof-carrying data** (as requested),
  so transformations can preserve/transport it and extraction can ignore it.

A good extracted artefact is:

- a corecursive definition whose operational unfolding corresponds to one
  observation step.

## Minimal engineering plan (incremental)

1. Introduce a second progress witness style (Büchi/parity) in `theories/Progress/`.
2. Define which rule edges count as “observable progress”.
3. Prove a graph-theoretic characterization (SCC-based) that is finite and
   extraction-friendly.
4. Only after that, decide whether to add object-level coinductive types
   (`cofix`) or keep productivity at the semantic layer.

## Summary

- Ranking progress (well-founded decrease) is great for inductive/termination
  arguments.
- Productive infinite behaviour (no bottom) needs a fairness-like condition
  (Büchi/parity) or bounded measures.
- We do **not** have to add coinductive types immediately; we can first add a
  Büchi/parity witness as an alternative `CyclicProof` witness.
- If we *do* add coinductives, we must add guarded corecursion and an
  observation/forcing semantics to make productivity meaningful.
