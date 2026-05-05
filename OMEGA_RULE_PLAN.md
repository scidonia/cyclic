# Omega Rule and Conditional CIU — Architecture Plan

## The Problem

`sorted (sort l) ≈_CIU true` cannot be proved by the SC alone.

The SC gets stuck at `sorted (insert x (sort l))` after one driving step.
It cannot fold back to `sorted (sort l)` because the goal is now about
`insert`, not `sort`. Standard anti-unification fails — the shapes differ.

## What Is Missing

### 1. Conditional CIU (hypothetical contextual equivalence)

Current framework: `supercompile_ciu_soundness_untyped` proves
*unconditional* CIU — `t ≈_CIU residual(t)` with no hypotheses.

Needed: **CIU under hypotheses**

```
Γ | H ⊢ t ≈_CIU u
```

where `H` is a set of equations `{ sᵢ ≈_CIU tᵢ }` that the SC may use
as rewrite rules during driving.

Proof-theoretic name: **open logical relations** / **hypothetical
contextual equivalence** (Pitts & Stark).

For our pure CBN language this degenerates to:

```
sorted l ⇓ true  →  sorted (insert x l) ⇓ true
```

i.e., convergence under a hypothesis about convergence.

### 2. Lemma-as-rewrite-rule in the driving step

The SC driving step (`drive_step` in Supercompile.v) currently only uses:
- β-reduction
- ι-reduction (case/constructor)
- δ-reduction (unfolding of fix)

Needed: **δ-reduction extended with a lemma environment**

```
Σ_lemmas : list (tm * tm)   (* (lhs, rhs) pairs, proved by sub-SC *)
```

During driving, after β/ι/δ, apply the first matching lemma rewrite.
This is **rewriting modulo proved equations** — the SC becomes a
conditional term rewriting system.

Architecture:

```coq
Definition drive_step_with_lemmas
    (Σenv : Ty.env)
    (lemmas : list (tm * tm))   (* proved: lhs ≈_CIU rhs *)
    (j : config) : list config
```

The lemma `sorted l = true → sorted (insert x l) = true` becomes the
rewrite rule `sorted (insert x ?0) → true` guarded by `sorted ?0 = true`.

### 3. LLM cut proposal

The LLM oracle needs to propose not just generalisations (anti-unification
results) but also **auxiliary lemmas** — statements that, if true, unblock
the main proof.

Interface:

```python
def propose_lemma(stuck_config, sigma, memo) -> optional[tm]:
    """
    Given a stuck configuration and current generalisation context,
    propose an auxiliary lemma that would unblock the SC.
    Returns a term (the lemma statement) or None.
    """
```

The kernel then:
1. Runs the SC on the proposed lemma independently
2. If `trace_condition_ok` passes, adds it to `Σ_lemmas`
3. Retries the main proof with the extended lemma environment

This is **iterated cut introduction** — the proof-theoretic analogue of
interactive theorem proving where a human says "I'll need a lemma about
insert first."

### 4. The ω-rule connection

The SC with cyclic backlinks already implements a form of the ω-rule:

```
∀ concrete n,  P(n) ⇓ true
─────────────────────────────   (ω-rule)
∀ n,  P(n) ≈_CIU true
```

The trace condition (`trace_condition_ok`) is the mechanised check that
the SC graph satisfies the progress condition — which corresponds to
**well-foundedness** of the induction, which is the hypothesis of the ω-rule.

For `sorted (sort l)`:
- All "offramps" (base cases: `l = nil`, already-sorted elements) reduce
  to `true` — ω-rule hypothesis for concrete inputs
- The recursive descent is structural on `l` — well-foundedness
- But the **induction step** requires the auxiliary lemma about `insert`

The auxiliary lemma is itself proved by the SC (induction on `l`), and
the main goal is proved using the lemma as a rewrite rule. Together this
is a **nested application of the ω-rule**: one cyclic proof inside another.

In proof theory: **mutual induction** or **lexicographic induction**.

## Implementation Plan

### Phase 1 — Lemma environment in driving (next)

1. Add `lemmas : list (tm * tm)` parameter to `drive_step`
2. After standard β/ι/δ, try each lemma as a left-to-right rewrite
3. Extend `supercompile_cfg` to carry `lemmas` through recursion
4. Add `supercompile_jTy_with_lemmas` entry point

Estimated effort: ~50 lines of Coq in `Supercompile.v`.

### Phase 2 — Sub-SC lemma validation

1. Given a proposed lemma `lhs ≈_CIU rhs`, run `supercompile_jTy_tc`
   on `lhs` with the existing lemma environment
2. Check the residual equals `rhs` (or is CIU-equivalent)
3. If `trace_condition_ok` passes, the lemma is proved and can be added

### Phase 3 — LLM lemma proposal

1. When the SC is stuck and neither AU nor speculation unblocks it,
   call `llm_propose_lemma` with the stuck config
2. The LLM returns a statement (e.g. `sorted (insert x ?0) = true`
   under hypothesis `sorted ?0 = true`)
3. The kernel attempts Phase 2; if it succeeds the lemma is trusted

### Phase 4 — Conditional CIU theorem

Extend `supercompile_ciu_soundness_untyped` to:

```coq
Theorem supercompile_ciu_soundness_conditional :
  ∀ Σenv fuel Γ t A lemmas v b,
    (∀ (lhs, rhs) ∈ lemmas, ciu lhs rhs) →
    supercompile_jTy_tc_with_lemmas fuel Σenv lemmas Γ t A = Some (v, b) →
    ciu t (residualise_cfg fuel Σenv b v 0 ∅).
```

The hypothesis `∀ (lhs, rhs) ∈ lemmas, ciu lhs rhs` is discharged by
Phase 2 for each lemma.

## Examples That Will Become Provable

Once Phase 1-4 are complete:

| Conjecture | Lemma needed | Discovered by |
|---|---|---|
| `sorted (sort l) ≈_CIU true` | `sorted l → sorted (insert x l)` | LLM |
| `sort (sort l) ≈_CIU sort l` | idempotence of sorted insert | LLM |
| `length (sort l) = length l` | sort preserves length | SC (no lemma) |
| `member x (sort l) = member x l` | sort preserves membership | LLM |
| `rev (rev l) ≈_CIU l` | `rev (append l1 l2) = append (rev l2) (rev l1)` | LLM |

Note: `rev (rev l)` is already proved by cyclic induction alone in our
current SC (it does not need the auxiliary lemma). It appears here as
a calibration point.

## What Is Already Working (No Changes Needed)

The following are provable right now with zero new infrastructure:

- All 8 examples in `HardExamples.v` (map fusion, accumulator, etc.)
- All 11 speculation conjectures in `SpeculationConjectures.v`
- `length (sort l) = length l` — once `sort` is defined (pure induction)
- `member x (insert x l) = true` — pure induction on `l`
- `sorted l → sorted (insert x l)` — pure induction on `l` (the key lemma)

These should be the next targets.
