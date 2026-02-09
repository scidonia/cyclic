# Reviewer-Response Checklist

This checklist is derived from `papers/cyclic-cic/reviewer_report.md` and tracks which concerns have been addressed in the paper.

## A. Scope/claims

- [ ] A1. State precise scope: research note vs journal article level.
- [ ] A2. Make the canonicalisation claim precise (what is guaranteed vs what is empirical/operational).

## B. Semantics and equality (requested self-containedness)

- [ ] B1. Define the semantic meaning of cyclic objects.
  - Target choice (author intent): **extracted-term semantics**.
- [ ] B2. Define the intended equality on cyclic objects.
  - Target choice (author intent): **same extracted term up to typed CIU**.
- [ ] B3. Explain what is in/out of the TCB (kernel definitional equality vs external normalization).

## C. Cyclic object model

- [ ] C1. Provide an explicit mathematical definition of cyclic objects used (graph, labels, buds/backlinks, substitution evidence).
- [ ] C2. Explain local correctness vs global progress condition in paper-level definitions.

## D. Supercompilation procedure

- [ ] D1. Provide a pseudo-code/algorithmic account of driving + control (whistle) + generalise + fold.
- [ ] D2. Clarify how dependent types/motives are treated by the transformations.
- [ ] D3. State what correctness is proved (CIU preservation of steps; what is not proved).

## E. Refolding soundness

- [ ] E1. Explain how progress witnesses prevent unsound refolding.
- [ ] E2. State/outline the invariants that must be preserved by fold/refold transforms.

## F. Canonicalisation payoff (examples)

- [ ] F1. Add an end-to-end example where two distinct terms/proofs converge to the same extracted normal form (up to CIU).
- [ ] F2. Add at least one example where CaseCase + information propagation is essential.
- [ ] F3. (Optional) Add an example that involves unfolding/generalisation/folding.

## G. Presentation cleanup

- [ ] G1. Remove redundant/confusing text in the theorems section.
- [ ] G2. Reduce “see file X” tone; keep file references but not as primary exposition.
- [ ] G3. Add a short note justifying CIU as the semantic equivalence.

## H. Source `fix` vs cyclic `fix-free`

- [ ] H1. Explain that `fix` may be reintroduced when mapping back from cyclic format.
- [ ] H2. Explain why cyclic intermediate form increases identification power.
