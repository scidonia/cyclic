# Backlink Admissibility for CoC with Inductives

## Goal

Prove that the `back` rule of the cyclic sequent calculus is admissible: every cyclic proof can be unfolded into a standard CIC proof with explicit induction (the CIC recursor/fix).

## Approach (Brotherston-Simpson style)

### Step 1: Unfolding

Given a cyclic proof graph with root `v0` and root label `jTy Γ t A`:

1. **Unfold** the graph: starting from the root, follow outgoing edges recursively.
   When hitting a backlink (edge from `v` to `v_prev` with substitution `σ`),
   substitute into the COMPANION's label and continue from `v_prev`'s successors.

   This produces an **infinite tree** where backlinks are eliminated by
   "unfolding" them — each backlink is replaced by the subtree rooted at
   the companion.

2. **The unfolded tree is locally correct**: at each node, the local rule is
   satisfied (because the original graph was locally correct by Claim 1).

3. **The unfolded tree is well-founded**: the budget trace (Claim 2) guarantees
   that every infinite path has infinitely many progress events. This ensures
   the tree has no infinite purely-async path.

### Step 2: Extracting an induction

The unfolded tree is an infinite but well-founded proof object. From it we
extract:

1. **A motive** — the type annotation of the root, generalised over the
   induction parameter.

2. **Base cases** — the leaves of the unfolded tree where the induction
   parameter reaches a base constructor.

3. **Step cases** — the internal nodes where a progress event (case-split)
   occurs and the recursive call goes to a structurally smaller instance.

4. **The induction principle** — the CIC recursor for the inductive type
   being split on at each progress event.

### Step 3: Proof of equivalence

Prove that the extracted standard proof is observationally equivalent to
the original cyclic proof (they have the same CIU semantics).

## Key difficulties

1. **Dependent motives**: the CIC recursor requires a motive that varies
   with the induction parameter. The cyclic proof's motives are `tCase`
   with binder types — these become the motive of the recursor.

2. **Multiple induction parameters**: a cyclic proof may contain multiple
   backlink cycles, each on a different inductive type. These must be
   disentangled into a single well-founded lexicographic order.

3. **Index normalisation**: the SC normalises type indices during driving.
   The standard proof must re-derive these normalisations via rewriting.

## Existing infrastructure

- `SupercompileTraceCheckSound.v`: trace condition soundness (used for
   Step 1.3 — ensures the unfolded tree is well-founded)
- `SupercompilationCorrespondence.v`: pre-proof and cyclic proof theorems
- `CaseCase.v`: motive propagation theorems
- `SplitNonInvertible.v`: non-invertibility of splitting

## Files to create

- `theories/Equiv/BacklinkAdmissible.v`: main theorem and proof
