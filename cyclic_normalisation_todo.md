# Cyclic proof normalisation TODO

This TODO covers the next development phase: defining *transformations on cyclic proofs* (graph proof objects) and proving they preserve the chosen semantic equivalence (CIU-style, values-as-observables; termination assumed).

## Conventions / prerequisites

- Proof objects: rooted cyclic preproofs / cyclic proofs (finite graph + local rule correctness + later global progress witness).
- Equivalence target:
  - term-level: `Equiv.CIU.ciu` (`theories/Equiv/CIU.v`)
  - proof-level (planned): `p ≈proof q  :=  ciu (extract p) (extract q)`
- During this phase, assume termination is established *before* applying CIU-equivalence statements.

## Phase 0 — Infrastructure for transformations

- [ ] Decide the exact proof object type that transformations act on
  - raw `ReadOff.builder` graphs vs `Preproof.rooted_preproof` vs full `CyclicProof`
- [ ] Define a “rewrite step” interface for proof-graph transforms
  - input: proof graph + designated root
  - output: transformed proof graph + root mapping
  - preserve: well-formedness (vertex closure), local correctness, progress witness transport (later)
- [ ] Define the semantic equivalence on proofs via extraction
  - `proof_equiv p q := ciu (extract p) (extract q)`
- [ ] Prove generic lemmas for composing transformations
  - reflexivity / transitivity of `proof_equiv`
  - if `T1` and `T2` preserve `proof_equiv`, so does `T2 ∘ T1`

## Phase 1 — Case–case commute (first real transform)

Goal: commute nested cases in the *cyclic proof universe*.

Informal term shape:

- from:
  - `case (case x as M in C1 => a | C2 => b | ...) as N in D => ...`
- to (distribute the outer case across branches of the inner case):
  - `case x as M in
      C1 => case a as N in D => ...
    | C2 => case b as N in D => ...
    | ...`

Tasks:

- [ ] Specify the syntactic side-condition(s)
  - which occurrences of `N` / binding structure is being commuted
  - ensure capture-avoidance and correct de Bruijn shifting
- [ ] Define the transform at the proof-graph level
  - identify the subgraph pattern corresponding to a `case` whose scrutinee is a `case`
  - produce a rewritten graph with duplicated outer-case structure across branches
  - ensure back-links/substitution evidence remain well-formed
- [ ] Prove the transform preserves term semantics (CIU)
  - statement: `ciu (extract p) (extract (commute_case_case p))`
  - assume termination for the terms involved
- [ ] (Optional) show it matches the expected term-level commute lemma
  - `extract (commute_case_case p)` is the commuting rewrite of `extract p`

## Phase 2 — Constructor elimination

Intuition: eliminate redundant `case (Roll ...)` forms (constructor-case reduction) at the cyclic proof level.

- [ ] Define the proof-graph rewrite for `case (roll ...)` to branch application
- [ ] Prove `ciu` preservation via extraction

## Phase 3 — Branch information propagation

Intuition: within a `case x`, refine branch-local knowledge (e.g. replace occurrences of `x` with the matching constructor form in the corresponding branch).

- [ ] Specify the exact propagation rule(s) (what is replaced, where)
- [ ] Implement the rewrite on the cyclic proof graph
- [ ] Prove `ciu` preservation via extraction

## Phase 4 — β-reduction and administrative normalisation

- [ ] β-reduction at proof-graph level (mirroring `step_beta`)
- [ ] Administrative rewrites (e.g. reassociation of apps, case scrutinee simplifications)
- [ ] Prove each rewrite preserves `ciu` (under termination)

## Phase 5 — Normalisation procedure (modulo back-links)

- [ ] Define a normalisation strategy as a relation or function
  - initially: a rewrite relation `p ~~>* p'`
  - later: a deterministic function (if possible)
- [ ] Show normalisation preserves `proof_equiv`
  - `proof_equiv p (normalize p)`
- [ ] Define a suitable normal form notion “modulo back-links”

## Phase 6 — Back-links, unfolding, and control (new strategy)

This is explicitly deferred until the above non-recursive rewrites are stable.

- [ ] Decide the operational meaning of back-links during normalisation
  - when to unfold vs when to treat as opaque
  - interaction with termination/progress witnesses
- [ ] Design a control strategy (fuel, SCC/ranking-guided, etc.)
- [ ] Prove soundness of the strategy wrt `proof_equiv`
