# Cyclic Proofs for a Dependent Type Theory (Sketch)

## Motivation

Canonical cyclic proofs are **intensional representatives** whose equality
soundly approximates **extensional program equivalence**.

The goal of this project is to design and mechanize (in Coq) a **cyclic proof
system** for a dependent type theory close to CoC, where:

- Proof objects are **finite graphs**, not trees
- Cycles are permitted locally
- Soundness is recovered via a **global condition**
- Equality/conversion is treated cyclically and intensionally

This document sketches the intended architecture and proof strategy.

---

## High-Level Structure

We separate proof objects from proof validity:

1. **Pre-proofs**  
   Finite, graph-shaped derivations with locally correct inference steps.

2. **Proofs**  
   Pre-proofs equipped with a *global soundness condition* (progress / ranking).

This mirrors standard cyclic proof theory:  
> *finite object + global condition = sound infinite meaning*

---

## Judgements

We assume a core dependent type theory with:

- Terms: `t, u`
- Types: `A, B`
- Contexts: `Γ`

Judgements include (initially):

- Typing (inductive):
  ```
  Γ ⊢ t : A
  ```

- Equality / conversion (cyclic):
  ```
  Γ ⊢ t ≈ u : A
  ```

Equality is **not judgmental equality** of CoC, but a *cyclicly justified*
relation on canonical/intensional representatives.

---

## Rules

Inference rules are given as relations:

```
Rule : Judgement → list Judgement → Prop
```

Example (informal):

- β-like rule (intensional):
  ```
  Γ ⊢ (λx. t) u ≈ t[u/x] : A
  ```

- Congruence rules
- Π-type extensionality rules (restricted, guarded)

Typing rules remain inductive and syntax-directed.
Equality rules may introduce cycles.

---

## Proof Objects: Finite Graphs

A **pre-proof** is a finite directed graph:

- Nodes = finite set (e.g. `Fin n`)
- Each node has:
  - a judgement label
  - a chosen rule instance
- Edges point from a conclusion node to its premise nodes

Formally:

- `label : node → Judgement`
- `succ  : node → list node`
- `rule_ok(n)`:
  ```
  Rule (label n) (map label (succ n))
  ```

Local correctness = all nodes satisfy `rule_ok`.

---

## Edge / Trace Structure

Not all edges are equal.

Edges (or rule instances) are annotated with:
- which *trace position* they correspond to
- whether they represent:
  - unfolding
  - structural descent
  - back-link / recursive use

This information is used **only** by the global soundness condition.

---

## Global Soundness Condition

A pre-proof becomes a proof only if it satisfies a *global progress condition*.

### Preferred approach: Ranking-based condition

- Assign a **well-founded measure** to nodes or trace positions:
  ```
  rank : node → Measure
  ```
- Require that:
  - Along any cycle, some distinguished edge strictly decreases `rank`
  - Other edges do not increase rank

This ensures that no infinite path can avoid progress.

Equivalent intuitions:
- every cycle contains a descent
- infinite unfolding yields a well-founded derivation tree

Alternative formulations (future work):
- trace fairness over infinite paths
- SCC-based progress witnesses

---

## Semantics and Soundness

Define a semantic interpretation:

```
⟦ Γ ⊢ t ≈ u : A ⟧ : Prop
```

(e.g. PER-style or logical relation semantics)

Main theorem:

```
If G is a finite graph
and G is locally correct
and G satisfies the global condition
and root ∈ G
then ⟦ label(root) ⟧ holds.
```

Thus:
```
PreProof + GlobalCondition ⇒ Semantic Validity
```

---

## Relationship to CoC

- This is **not** standard CoC judgmental equality
- Cyclic equality approximates extensional equivalence
- Typing remains inductive
- Equality is intensional and justified cyclically

Universes are *not* included initially.

---

## Intended Development Plan

1. Dependent λ-calculus with Π-types (no universes)
2. Inductive typing, cyclic equality
3. Graph-based proof objects
4. Ranking-based soundness theorem
5. Mechanization in Coq
6. Later extensions:
   - inductive/coinductive types
   - limited universes
   - stronger extensional principles

---

## Conceptual Positioning

This system sits between:

- cyclic proof theory (Brotherston-style)
- PER/logical-relation models of type theory
- normalization-by-evaluation
- guarded recursion

but is **proof-theoretic** and **intensional**.

---

## Key Slogan

> *Canonical cyclic proofs are intensional representatives whose equality
> soundly approximates extensional program equivalence.*
