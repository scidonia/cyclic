# Reviewer Critique: Supercompilation as Cyclic Proof Search for CoC

## Overall Assessment

This paper makes an important novel contribution (first supercompilation for dependent types) but suffers from significant structural and presentational issues that prevent it from being publication-ready. The core technical content is sound, but the paper reads more like working notes than a polished research article. Comparison with the companion paper "A Cyclic Calculus of Inductive Constructions" reveals several areas where this paper falls short of professional standards.

## Major Issues

### 1. **Lack of Concrete Formal Theorems**

**Problem**: Sections 4 and 6 are filled with placeholders, "intended" theorems, and informal statements. The paper promises formal results but doesn't deliver them.

**Evidence**:
- Section 4.7: "Bisimulation theorem" with no actual theorem statement
- Section 6: "Equivalence statements (targets)" - all theorems are marked "(placeholder)"
- Definition 1.1: "Operational move correspondence (placeholder)"
- Multiple "TODO" comments visible in Section 4

**Comparison**: The cyclic-cic paper (Section 9) lists concrete mechanized theorems with references to Coq files:
- "Theorem 9.1 (Typed CIU equivalence). Mechanized in Equiv/CIU.v"
- "Theorem 9.3 (Read-off/extraction round-trip). Proved in Transform/ReadOffExtractCorrectness.v"

**Required Fix**: Replace all placeholders with actual theorem statements, even if proofs are incomplete. State theorems formally with quantifiers, hypotheses, and conclusions.

### 2. **Missing Mechanization Details**

**Problem**: Section 8 ("Mechanisation plan in Coq") is vague and reads like a TODO list rather than documentation of completed work.

**Evidence**:
- "We plan to mechanise..." (future tense throughout)
- No concrete file references or line numbers
- No discussion of what's actually proved vs. admitted

**Comparison**: The cyclic-cic paper explicitly lists:
- Coq file names and theorem names
- What is mechanized and what remains
- Concrete examples with specific lemma references

**Required Fix**: 
- Change to "Mechanization Status in Coq"
- List actual files, modules, and theorems
- Distinguish proved theorems from admitted ones
- Provide concrete pointers (e.g., "SupercompilationCorrespondence.v:183-205")

### 3. **Examples Lack Worked Details**

**Problem**: Section 4.6 "Concrete correspondence examples" shows SC state and proof rules but doesn't demonstrate the actual correspondence with enough rigor.

**Evidence**:
- Examples show "Why they're the same" but with hand-wavy explanations
- No formal bisimulation relation applied to examples
- Missing: vertex labels, edge mappings, rule validation details

**Comparison**: The cyclic-cic paper (Section 8.3, 8.6) provides:
- Complete term sequences with explicit substitutions
- Step-by-step graph construction
- Concrete Coq output from mechanized examples

**Required Fix**: 
- Add at least one fully worked example showing exact vertex labels, edges, and bisimulation witnesses
- Include Coq-generated output or proof snippets
- Make the correspondence mechanically checkable

### 4. **Section 7 (LLM Oracle) Feels Out of Place**

**Problem**: The LLM oracle section is speculative and doesn't fit the technical rigor of the rest of the paper. It reads like a proposal rather than completed research.

**Evidence**:
- "Why an LLM could help" - pure speculation
- "Risks and evaluation" - no actual evaluation performed
- No implementation, no experiments, no data

**Comparison**: The cyclic-cic paper sticks to completed, mechanized results throughout.

**Recommendation**: 
- Either remove this section entirely, OR
- Move to "Future Work" in conclusion, OR
- If keeping, add concrete implementation and experimental results

### 5. **Notation Inconsistencies**

**Problem**: Multiple notational systems used without clear distinctions.

**Evidence**:
- Section 2: Uses `\PiTy`, `\Lam`, `\App` macros
- Section 3: Mixes these with plain text descriptions
- Section 4: Introduces SC notation (`SC.drive_cbn_once`) without formal definition
- Judgement forms: `jTy`, `jObs`, `jSub` introduced but not used consistently

**Required Fix**:
- Define all notation in one place (Section 2 or appendix)
- Use consistent notation throughout
- Add a notation index/glossary

### 6. **Missing Proofs or Proof Sketches**

**Problem**: No actual proofs are shown, even in appendices.

**Comparison**: The cyclic-cic paper (Section 9) at least acknowledges what's proved and provides intuition for key lemmas.

**Required Fix**:
- Add appendix with key proof sketches
- Or at minimum, explain proof strategies for main theorems
- Show at least one complete inductive proof

### 7. **Weak Introduction**

**Problem**: Section 1 is titled "Thesis and shape of equivalence" but doesn't provide a proper introduction to the paper.

**Missing**:
- No problem statement
- No motivating example upfront
- No overview of contributions
- Jumps straight to technical definition

**Comparison**: The cyclic-cic paper has a proper introduction (Section 1) with:
- Clear motivation (Figure 1 showing pipeline)
- Concrete examples (index bureaucracy)
- Overview of claims and scope

**Required Fix**: 
- Add proper Introduction section (before Section 1)
- Include motivating example (maybe length-map fusion)
- List contributions explicitly
- Provide paper roadmap

### 8. **Conclusion is Too Brief**

**Problem**: Section 9 is 3 sentences and reads like an excuse.

**Quote**: "This document is a working outline. Immediate next steps are..."

**Comparison**: The cyclic-cic paper conclusion (Section 11) summarizes achievements and discusses future work properly.

**Required Fix**:
- Expand to proper conclusion (at least 1 page)
- Summarize contributions
- Discuss limitations
- Outline future work with concrete plans

## Minor Issues

### 9. **Inconsistent Section Depth**

- Section 2 (Calculus) is very detailed
- Section 3 (Sequent Calculus) is very detailed  
- Section 4 (Correspondence) is sparse with many subsection stubs
- Sections 5-9 feel rushed

**Fix**: Balance section lengths. Either compress 2-3 or expand 4-9.

### 10. **Missing Cross-References**

**Examples**:
- Section 3.9: "Section ??" (broken reference)
- Many forward references to undefined sections
- No back-references from later sections to definitions

**Fix**: Complete all cross-references.

### 11. **Figure Quality**

**Problem**: No figures! This is a paper about graph structures.

**Comparison**: Cyclic-cic paper has Figure 1 (normalization pipeline) and Figure 2 (proof graph example).

**Required**: Add at least 3 figures:
- Bisimulation diagram showing SC graph ↔ Proof graph
- Example cyclic proof graph for length-map
- Correspondence table (SC operation → Sequent rule)

### 12. **Abstract Makes Strong Claims Without Support**

**Quote**: "This correspondence is formalized through a bisimulation... mechanized in Coq"

**Reality**: The bisimulation is stated but not proved. Many admits remain in the Coq code.

**Fix**: Soften claims or complete mechanization before submission.

### 13. **Related Work Positioning**

**Good**: Comprehensive coverage of prior work

**Problem**: Doesn't clearly explain what makes this work *harder* than prior supercompilation work (beyond "dependent types").

**Fix**: Add subsection explaining technical challenges specific to dependent types:
- Type dependencies during driving
- Context management in branches
- Preservation of typing during folding
- CIU for dependent types

### 14. **Missing Comparison Table**

**Needed**: A table comparing:
- Classical supercompilation vs. this work
- Natural deduction proofs vs. cyclic proofs
- Fixed induction vs. post-hoc induction

### 15. **Terminology Confusion**

**Problem**: "Focused" appears in title but focusing discipline is not formally defined.

**Evidence**: Section 3.7 explains phases but doesn't give formal focusing judgment.

**Fix**: Either:
- Formally define focusing with judgment forms, OR
- Remove "focused" from title if it's just informal discipline

## Critical Omissions

### 16. **No Algorithm Pseudocode**

The paper describes supercompilation and proof search but never gives actual algorithms.

**Needed**:
- Pseudocode for supercompilation main loop
- Pseudocode for proof search with focusing
- Formal bisimulation algorithm

### 17. **No Complexity Analysis**

- Is proof search decidable?
- What's the complexity of checking bisimulation?
- Termination guarantees?

### 18. **No Evaluation**

- No examples run through the implementation
- No performance numbers
- No comparison with other approaches

**Note**: This may be acceptable for a pure theory paper, but then don't claim it's "mechanized in Coq" so prominently.

## Checklist for Publication Readiness

### Structure Fixes (Critical)

- [ ] Add proper Introduction section with motivation
- [ ] Replace all "(placeholder)" theorems with actual statements
- [ ] Add formal bisimulation definition and theorem statement
- [ ] Complete all "TODO" items or remove them
- [ ] Fix all "Section ??" broken references
- [ ] Expand conclusion to proper length
- [ ] Decide on LLM section: remove, shrink to future work, or add evaluation

### Content Fixes (Critical)

- [ ] Add at least one fully worked correspondence example
- [ ] Show formal bisimulation application to example
- [ ] Add proof sketches for main theorems (appendix OK)
- [ ] Clarify mechanization status (what's proved, what's admitted)
- [ ] Add algorithm pseudocode for SC and proof search
- [ ] Define focusing discipline formally or remove from title

### Presentation Fixes (Important)

- [ ] Add 3-5 figures (bisimulation, proof graph, correspondence table)
- [ ] Create notation glossary
- [ ] Make notation consistent throughout
- [ ] Add comparison table (this work vs. prior work)
- [ ] Add technical challenges subsection to related work
- [ ] Balance section lengths

### Polish Fixes (Minor but Necessary)

- [ ] Complete all cross-references
- [ ] Add line numbers for submission
- [ ] Check all citations are complete
- [ ] Spell check
- [ ] Consistent capitalization (e.g., "Supercompilation" vs. "supercompilation")
- [ ] Abstract should match actual paper contents

### Optional Improvements

- [ ] Add complexity analysis
- [ ] Add evaluation section with examples
- [ ] Add performance measurements
- [ ] Compare with other proof assistants
- [ ] Discuss practical applications

## Recommendation

**Current Status**: Reject - Major Revision Needed

**Reasoning**: The paper contains important and novel ideas (first supercompilation for dependent types) but is presented more as a technical report or working notes than a polished research article. The mechanization claims are overstated, too many theorems are placeholders, and the structure needs significant work.

**Path Forward**: 

1. **Short term (2-3 weeks)**:
   - Complete all theorem statements (even without full proofs)
   - Add worked examples with full details
   - Fix structure issues (intro, conclusion)
   - Remove or relocate LLM speculation section
   - Add figures

2. **Medium term (1-2 months)**:
   - Complete mechanization or clearly document admits
   - Add proof sketches for key results
   - Add evaluation with concrete examples
   - Write proper related work positioning

3. **Long term (3-4 months)**:
   - Complete all proofs in Coq
   - Add performance evaluation
   - Consider splitting into two papers:
     - Paper 1: Theory (this paper, focused and polished)
     - Paper 2: Implementation and Evaluation

## Comparison with Cyclic-CIC Paper

The companion paper is significantly stronger:

| Aspect | Cyclic-CIC | This Paper |
|--------|-----------|------------|
| Theorem statements | Complete and formal | Many placeholders |
| Mechanization | Explicit file references | Vague "plan" |
| Examples | Fully worked with output | Hand-wavy explanations |
| Figures | 2 clear diagrams | None |
| Introduction | Proper motivation | Jumps to technical details |
| Conclusion | Substantive | 3 sentences |
| Speculation | None | Full section on LLMs |

The current paper should be revised to match the quality standards of the cyclic-cic paper.
