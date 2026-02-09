# Reviewer Report (critical, journal-style)

Manuscript: *A Cyclic Calculus of Inductive Constructions: Escaping the Bureaucracy of Inductive/Recursive Syntax*

## 1. Summary and overall assessment

The manuscript proposes a CIC-like setting in which recursive proof structure is represented as cycles in a finite proof graph rather than via a fixed syntactic recursion operator (`fix`) or a fixed family of elimination/induction schemata. Soundness is ensured by a global progress condition on cycles. The paper further advocates a “supercompilation-style” normalization procedure (driving + information propagation + commuting conversions + unfold/fold + generalization under a termination control) as a way to canonicalize such cyclic proofs and thereby *eliminate proof bureaucracy*: after CIU-preserving transformations and refolding, distinct syntactic derivations may collapse to the same cyclic representative.

The work is compelling as a research programme and is supported by a non-trivial mechanization in Coq (typed CIU preservation for head beta; CaseCase; read-off/extraction round-trip; a ranking template for the global condition; and an implemented CIU theorem for scrutinee propagation). The paper, however, currently reads more like an extended design note than a finished journal article: key definitions are informal or only sketched at the paper level, the canonicalization claim is not demonstrated end-to-end on a substantial case study, and several crucial components of “supercompilation” are described at a high level without enough formal detail to assess correctness or feasibility.

My recommendation is **major revision**. The core thesis is interesting and could be publishable in a high-quality venue, but the paper needs stronger formal articulation of the cyclic proof object semantics and a clearer, more convincing story about what is actually obtained (and what is not) with respect to definitional equality, proof identity, and practical proof engineering.

## 2. Claimed contributions vs. what is delivered

The abstract and introduction promise:

- a cyclic CIC-like calculus with proof graphs and a global progress condition;
- a supercompilation-style normalization procedure enabling post-hoc proof identity;
- mechanized metatheory and semantic preservation results.

The mechanization appears substantive and is a genuine strength. However, at the paper level:

- The *cyclic proof object language* and its relationship to the source calculus is only partially formalized in the text. The reader is asked to trust that the Coq development matches the described structure, but the paper does not give enough self-contained definitions of:
  - what the cyclic graph objects are (beyond informal prose and a few label lists),
  - what notion of equivalence/isomorphism is intended for “canonical representatives”,
  - what the “meaning” of a cyclic proof object is (unfolding semantics? denotational semantics? reduction to source terms?) and which of these is used in theorems.

- The “supercompilation bundle” is listed clearly (Section `sections/transformations.tex`), but the paper does not specify the *actual algorithm* (driving strategy, generalization policy, fold matching, termination control integration, and interaction with types/indices). Without this, it is hard to evaluate the claim that the approach yields canonical cyclic representatives in practice.

- The canonicalization claim is explicitly qualified (good), but the paper does not provide a concrete end-to-end example where two distinct proofs normalize to the *same* cyclic representative. The opening motivation examples are helpful but do not yet show the main payoff.

## 3. Strengths

1. **Strong motivating thesis, well-articulated**: the idea that “the induction principle need not be fixed syntactically” is crisp, and the paper explains the syntactic-bureaucracy problem in a way that will resonate with proof engineers.

2. **Useful motivating examples early** (`sections/why-cyclic.tex`): the cyclic Even/Odd sketch and the dependent-index transport example concretely show the two sources of pain: recursive structure bureaucracy and definitional equality brittleness.

3. **Mechanized semantic preservation results** (`sections/theorems.tex`): grounding transformation claims in a CIU-style semantics is appropriate for a call-by-name operational setting and avoids handwavy “obviously semantics-preserving” arguments.

4. **Clean separation of local correctness vs global progress** (`sections/global-conditions.tex`): the paper correctly emphasizes that cyclicity requires a global invariant and that transformations must transport/rebuild progress evidence.

5. **Alignment with known program transformation literature** (`sections/related-work.tex` + `sections/canonical-forms.tex`): tying the control relation to homeomorphic embedding / wqo and positioning fold/refold as memoization/generalization is conceptually sound.

## 4. Major weaknesses / required revisions

### 4.1. The paper is not self-contained enough

The manuscript repeatedly references Coq files as the “real” definitions. For journal publication, the paper must stand on its own to a greater degree. At minimum, I would expect:

- A precise mathematical definition of the cyclic proof object(s) used in the meta-theory, including:
  - the underlying graph structure (nodes/edges, rooting),
  - node labels (judgements, rule instances),
  - the backlink/bud/companion discipline,
  - what exactly substitution evidence is (syntax and typing),
  - how local correctness is checked.

- A clear semantics for cyclic proof objects:
  - either an unfolding semantics (possibly coinductive),
  - or a compilation/extraction semantics to the source term calculus,
  - and which semantics is used for the CIU preservation story.

Right now, the reader is left with a conceptual picture but not a formally checkable statement.

### 4.2. The canonicalization story is under-evidenced

The paper’s most distinctive claim is that after normalization/refolding, distinct proofs may become literally the same cyclic object. This is plausible, but it needs a concrete demonstration:

- Provide a worked example of two distinct source proofs/terms that normalize (via the proposed supercompilation bundle) to isomorphic/identical cyclic graphs.
- Show explicitly which transformations are applied and why they are admissible under the control relation.
- Clarify whether “same cyclic object” is meant modulo graph isomorphism, bisimulation, or a more refined quotient.

The current manuscript states the aspiration but does not yet exhibit it.

### 4.3. “Supercompilation” needs a more precise operational account

Section `sections/transformations.tex` enumerates the ingredients of supercompilation. For a journal audience, this should be strengthened along three dimensions:

1. **Algorithmic specification**: What is the driving strategy? How are generalization and folding chosen? What is memoized? What is the exact whistle condition, and at what granularity (terms vs typed judgements)?

2. **Interaction with dependent types**: The paper’s motivation is strongly dependent-typed, but the transformation descriptions are largely term-level. It must be clarified:
   - which transformations rewrite types/motives/indices,
   - whether normalization is intended to occur under binders in types, and
   - how the procedure avoids breaking definitional equality properties relied upon by the kernel.

3. **Correctness criteria**: CIU equivalence is the chosen semantics, but for canonicalization one also needs a notion of *stability* and *confluence modulo control*. What is the expected uniqueness property of the produced normal forms?

Without more detail, “supercompilation” functions as a metaphor rather than a concrete method.

### 4.4. Dependent case elimination is delicate; the paper should be explicit

The manuscript correctly describes dependent motives, and the operational semantics presents case-of-constructor reduction as returning the branch applied to arguments (with dependence tracked in typing). This is fine, but the paper should acknowledge the underlying design choice explicitly:

- In intensional type theory, dependent elimination often involves transports (or their definitional equalities). Here, the runtime term language erases them and relies on typing to account for dependence.
- The paper should state precisely which definitional equalities are assumed/aimed for, and how they relate to the extraction/read-off pipeline.

### 4.5. Theorems section has presentation issues

In `sections/theorems.tex`, the CaseCase subsection includes redundant/confusing text:

- It states correspondence to the Coq theorem, then mentions “infrastructure is in place”, then states again that it corresponds to the proved theorem. This should be tightened.

More generally, theorems should include (at least informally) the key hypotheses and the structure of the proof obligations, rather than only pointing to file names.

## 5. Specific questions to the authors

1. **What is the intended equality on cyclic proof objects?** Is it graph isomorphism, bisimulation, or something like “same extracted term up to CIU”? This choice matters for the canonical representative claim.

2. **What exactly is the semantic notion of a cyclic proof object?** Is it:
   - the infinite unfolding (tree) semantics,
   - the extracted term semantics,
   - or a denotational semantics? Which one is preserved by transformations?

3. **How do you avoid unsound refolding?** The global progress condition is a template, but what does it look like for the extracted vertex language, and how is it transported across fold/refold transformations?

4. **How strong is the canonicalization goal?** Do you expect uniqueness of normal forms under the supercompilation procedure, or merely that the procedure often reduces bureaucratic differences?

5. **What is the scope of the term calculus?** The current syntax includes `fix` in the source language, but the cyclic representation is “fix-free”. Is the long-term goal to remove `fix` entirely from the user-facing calculus, or is it only an internal compilation target?

## 6. Suggestions for improvement (actionable)

- Add a dedicated subsection that formally defines the cyclic object model used in Coq (graph, labels, buds/companions, substitution evidence), independent of implementation details.

- Include a worked running example that is normalized through:
  1) extraction to cyclic graph,
  2) a non-trivial sequence of CIU-preserving rewrites (CaseCase + beta + information propagation),
  3) at least one fold/refold step, and
  4) re-extraction, demonstrating proof identity/canonicalization.

- Expand the “supercompilation” section with a clear pseudo-code algorithm and a precise statement of what is proved about it (termination? soundness? partial correctness? stability?).

- Clarify the relationship to kernel definitional equality: what remains definitional, what becomes propositional, and where the cyclic normalization is intended to sit in the trusted computing base.

- Clean up theorems presentation: avoid repetition; ensure each theorem statement is unambiguous and lists all relevant hypotheses.

## 7. Minor comments / editorial

- The title is evocative but long; consider tightening for a journal format.

- The Even/Odd figure uses a natural-deduction style that is visually dense; consider either simplifying the example or adding a short textual explanation of the cycle and substitution witness.

- Consider adding a short note on why CIU (as opposed to contextual equivalence or logical relations) is the right equivalence for this setting, and what limitations it has.

- Several sections are written in a “notes” tone (“the file X defines…”) rather than a journal exposition tone. This is acceptable in a technical report but should be revised for publication.

## 8. Verdict

**Major revision.**

The core idea is strong and the mechanization is promising. To meet the bar of a high-quality journal, the paper needs more self-contained formal content and a compelling end-to-end demonstration of the canonicalization claim (or a more modest and precisely stated claim).