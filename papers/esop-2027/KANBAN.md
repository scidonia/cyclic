# KANBAN: Restructured Claims for Supercompilation Paper

## Claim Pipeline

```
supercompile_jTy success
         │
         ▼ (1) proved: all_supercompiled_programs_yield_preproof
  rooted_preproof (∀ vertex, local rule holds; domain/succ well-formed)
         │
         ▼ (2) in progress: cycle progress proved, full ranking to do
  cyclic_proof (global trace condition satisfied)
         │
         ▼ (3) to prove: CIU soundness theorem
  residual(t) ≈ciu t  (CIU equivalence under all closing substitutions)
         │
         ▼ (4) demonstrated: CIU checklist examples
  Examples pass (length-map, append, take-drop, vec-index, etc.)
```

---

## Items

### Item 1: Restructure core claims in thesis.tex
**Status:** `[ ]`
**Priority:** HIGH
**Dependencies:** None (can be done first)

Rewrite `sections/thesis.tex` to present the four claims as a numbered pipeline.
Each claim gets a formal statement (theorem/conjecture) + narrative prose.
Explicit dependency arrows between claims.
Status markers: (proved), (in progress), (conjectured), (demonstrated).

**Files:** `papers/cyclic-sequent-supercomp/sections/thesis.tex`
**Coq anchors:**
- Claim 1: `all_supercompiled_programs_yield_preproof` (SupercompilationCorrespondence.v:1659)
- Claim 1: drive/split/fold correspondence (SupercompilationCorrespondence.v:465, 513, 581)
- Claim 2: `supercompile_tc_cycle_progress` (SupercompilationCorrespondence.v:1699)
- Claim 2: `supercompile_satisfies_trace_condition` (SupercompilationCorrespondence.v:1718, axiom)
- Claim 3: CIU definition (CIU.v:21)
- Claim 4: CIU checklist (SupercompileChecklistIndexPipeline.v)

---

### Item 2: Prove full trace condition
**Status:** `[ ]`
**Priority:** HIGH
**Dependencies:** None (Coq proof, independent of paper text)

Currently `supercompile_satisfies_trace_condition` is an axiom at SupercompilationCorrespondence.v:1718.
Need to:
- Prove a decreasing trace ranking for progress edges in SC-generated graphs
- Connect to the existing `CyclicTraceCondition.v` infrastructure
- Replace the axiom with a proper theorem

**Sub-items:**
- [ ] 2a. Study `CyclicTraceCondition.v` / `CyclicTraceConditionBudget.v` / `CyclicTraceConditionObsTree.v` for the trace model
- [ ] 2b. Define the ranking function on SC config graph vertices
- [ ] 2c. Prove ranking decreases on progress edges (case-split edges)
- [ ] 2d. Prove ranking is well-founded (no infinite descent chains)
- [ ] 2e. Replace axiom with proved theorem

**Files:** `theories/Transform/SupercompilationCorrespondence.v`, `theories/Transform/CyclicTraceCondition*.v`

---

### Item 3: Prove CIU soundness
**Status:** `[ ]`
**Priority:** HIGH
**Dependencies:** Item 2 (needs cyclic proof status first)

Prove: if SC yields a valid cyclic proof with root v, then the residualised/read-off term is CIU-equivalent to the original input term.

Need to:
- Formalise the read-off/residualisation pipeline for the SC graph
- Relate the graph's vertex labels (which are jDrive configs) to the operational semantics
- Show that the cyclic proof soundness implies CIU equivalence of the extracted term
- This likely requires bisimulation between the SC graph and the CBN evaluation of the residual

**Sub-items:**
- [ ] 3a. Formalise "read-off" from cfg_builder to a residual term
- [ ] 3b. State the CIU soundness theorem formally
- [ ] 3c. Prove the theorem (may require substantial bisimulation work)
- [ ] 3d. Add the theorem statement to the equivalence section of the paper

**Files:** `theories/Equiv/CIU.v`, `theories/Transform/SupercompilationCorrespondence.v`, new file possibly needed

---

### Item 4: Rewrite equivalence.tex
**Status:** `[ ]`
**Priority:** HIGH
**Dependencies:** Item 1 (needs the claim structure defined first)

Rewrite `sections/equivalence.tex` to reflect the four-tier claim structure.
Replace the current "placeholder conjecture" format with proper pipeline presentation.
Each subsection corresponds to one tier of the claim pipeline.

**Files:** `papers/cyclic-sequent-supercomp/sections/equivalence.tex`

---

### Item 5: Update mechanisation-plan.tex
**Status:** `[ ]`
**Priority:** MEDIUM
**Dependencies:** Items 1-4

Align the mechanisation status table with the claim pipeline.
Show which Coq artifacts support each tier.
Distinguish proved / in-progress / planned clearly.

**Files:** `papers/cyclic-sequent-supercomp/sections/mechanisation-plan.tex`

---

### Item 6: Update conclusion.tex and abstract
**Status:** `[ ]`
**Priority:** MEDIUM
**Dependencies:** Items 1-5

Rewrite conclusion to summarise the pipeline, what's proved, what remains.
Update abstract to reflect the tiered structure.

**Files:** `papers/cyclic-sequent-supercomp/sections/conclusion.tex`, `papers/cyclic-sequent-supercomp/main.tex`

---

### Item 7: Add example validation section
**Status:** `[ ]`
**Priority:** MEDIUM
**Dependencies:** Items 1-4

Link the CIU checklist examples (SupercompileChecklistIndexPipeline.v) to claim (4).
Show the concrete programs, their residuals, and the computational equality proofs.

**Files:** `papers/cyclic-sequent-supercomp/sections/examples.tex` (extend existing section)

---

## Dependency Graph

```
Item 1 (thesis.tex) ──→ Item 4 (equivalence.tex)
                   ──→ Item 5 (mechanisation)
                   ──→ Item 6 (conclusion/abstract)
                   ──→ Item 7 (examples)
Item 2 (trace proof) ──→ Item 3 (CIU proof)
                     ──→ Item 5 (mechanisation)
Item 3 (CIU proof) ──→ Item 5 (mechanisation)
```

## Current State

| Claim | Coq Status | Paper Status |
|-------|-----------|-------------|
| 1. SC → pre-proof | **Proved** | Needs formal statement in thesis.tex |
| 2. +trace → cyclic proof | Cycle progress proved; ranking **axiom** | Needs theorem statement + "in progress" note |
| 3. cyclic proof → CIU equivalence | **Not started** | Needs conjecture statement |
| 4. Examples validate | **Demonstrated** via vm_compute | Has examples section, needs CIU linkage |
