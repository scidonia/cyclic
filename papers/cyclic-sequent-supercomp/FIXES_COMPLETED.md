# Reviewer Checklist Progress Report

## Completed Fixes (Session 1)

### A. Truthfulness & Scope ✓

- [x] **Toned down abstract mechanization claim** to match reality: "with core definitions and step-level lemmas mechanized in Coq; completing the full end-to-end correspondence proofs is ongoing"
- [x] **Removed all "placeholder" labels** from definitions and theorems
- [x] **Replaced placeholder theorems with formal conjectures** in Section 6 (now "Equivalence statements and status")
- [x] **Fixed broken cross-reference** (Section ?? → Section~\ref{sec:equiv})
- [x] **Added Mechanization Status section** (Section 8) with:
  - Table listing Coq files and theorem status
  - Clear "proved vs admitted vs stated" breakdown
  - Concrete file paths (e.g., `theories/Progress/PatternUnification.v`)

### C. Technical Precision ✓

- [x] **Clarified CBN operational semantics**: Fixed misleading claim about reducing under binders
  - Now: "CBN reduces at the outermost (head) position... We do not reduce under binders in the operational semantics"
  - Distinguishes operational semantics from definitional equality
- [x] **Added neutral/stuck definitions**: "A scrutinee is neutral when it cannot take an asynchronous driving step... stuck when it is neutral and no further commuting conversions apply"
- [x] **Fixed n-ary split rule presentation**: Replaced `TrinaryInfC` with proper n-ary inference rule schema using `\Infer` macro

### D. Paper Craft / Structure ✓

- [x] **Added proper Introduction** (Section 1):
  - Problem statement (supercompilation for dependent types)
  - Gap (no prior exposition for dependent types)
  - Contributions (5 bullet points)
  - Outline paragraph
- [x] **Replaced "working outline" conclusion** with journal-style conclusion:
  - Summary of contributions
  - Limitations paragraph
  - Future work paragraph
  - No more "this is a working outline" language
- [x] **Removed "placeholder" from Definition 1.1** (Operational move correspondence)

### Paper Statistics

- **Before**: 22 pages with major structural issues
- **After**: 23 pages with improved structure
- **Build status**: Compiles cleanly (only hyperref Unicode warnings)

## Remaining High-Priority Items

### A. Truthfulness & Scope (Remaining)

- [ ] Verify all cross-references are working (most fixed, need full check)

### B. Sequent Calculus Completeness

- [ ] **Critical**: Decide scope explicitly and document it
  - Option A: "Sequent system for SC correspondence" (scoped down, honest)
  - Option B: Add CIC sequent rule stubs (Π/λ/app, conversion, universes)
- [ ] Add stubs or full rules for:
  - Π/λ/application in sequent form
  - Conversion/definitional equality handling
  - Universes/cumulativity
  - Full dependent elimination obligations

### C. Technical Precision (Remaining)

- [ ] **Critical**: Add at least one fully worked correspondence example
  - SC configuration with explicit labels
  - Proof graph node with explicit label
  - Bisimulation mapping shown concretely
  - Rule instance verified step-by-step

### D. Paper Craft (Remaining)

- [ ] **High priority**: Add 2-4 figures:
  - [ ] SC graph ↔ proof graph mapping diagram
  - [ ] Example cyclic proof graph (length-map with progress edge marked)
  - [ ] Correspondence table (operations ↔ rules)
  - [ ] Optional: Pipeline diagram like cyclic-cic paper

### E. Novelty Claims (Remaining)

- [ ] Add "What is hard about dependent types?" subsection to related work
  - Typing preservation during folding
  - Context management in branches
  - Motive formation
  - CIU for dependent types

### F. Optional Improvements

- [ ] Trim or relocate LLM oracle section (Section 7)
  - Either: Move to future work in conclusion
  - Or: Add implementation/evaluation
  - Or: Remove entirely
- [ ] Add algorithm pseudocode for SC + proof search
- [ ] Consider adding small evaluation section

## Summary of Changes Made

### Files Modified

1. **main.tex**: Toned down mechanization claim in abstract
2. **sections/thesis.tex**: 
   - Completely rewritten as proper Introduction
   - Added contributions, outline, problem statement
   - Removed "placeholder" from definition
   - Fixed section references
3. **sections/calculus.tex**: Fixed CBN clarification
4. **sections/focused-cyclic-sequents.tex**:
   - Fixed split rule to n-ary schema
   - Added neutral/stuck definitions
   - Fixed broken reference
5. **sections/equivalence.tex**:
   - Renamed to "Equivalence statements and status"
   - Replaced placeholder theorems with conjectures
   - Linked to mechanization status section
6. **sections/mechanisation-plan.tex**:
   - Renamed to "Mechanization status in Coq"
   - Rewritten with concrete table of Coq artifacts
   - Listed proved vs admitted vs stated
7. **sections/conclusion.tex**:
   - Complete rewrite: journal-style conclusion
   - Contributions, limitations, future work
   - Removed "working outline" tone

### New Files Created

1. **REVIEWER_CHECKLIST.md**: Full checklist from reviewer critique
2. **REVIEWER_CRITIQUE.md**: Detailed reviewer report with comparison to cyclic-cic paper
3. **FIXES_COMPLETED.md**: This file

## Next Session Priorities (Ordered by Impact)

1. **Add scope decision paragraph** (Section 3 or Introduction): Clarify whether this is "full CIC sequent calculus" or "sequent system for SC correspondence"

2. **Add at least one figure**: Even a hand-drawn scan would help. Priority: SC ↔ proof graph mapping

3. **Fully worked example**: Take Example 1 or 2 from Section 4.6 and show:
   - Exact vertex labels (not just "Config: ...")
   - Exact bisimulation witness application
   - Rule validation step-by-step

4. **Add "challenges" subsection** to related work explaining what's technically hard about dependent types vs. prior SC work

5. **Consider LLM section**: Decide to trim/move/remove

The paper is now significantly stronger and more honest about mechanization status. Main remaining weakness is lack of figures and fully worked examples.
