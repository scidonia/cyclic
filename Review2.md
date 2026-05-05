# 📄 ICFP Review: Mechanisation Guides Design: Higher-Level Supercompilation via Sequent Calculus

---

## ⭐ Summary

This paper presents a mechanised account of higher-level supercompilation (HLS) grounded in a sequent-calculus interpretation of supercompilation as cyclic proof search. The authors identify three gaps in standard supercompilation:

1. Generalisation as cut introduction  
2. Speculation as variable projection  
3. Strengthened induction as the ω-rule  

They implement a four-layer architecture combining:
- anti-unification,
- speculation via dependency analysis,
- an LLM-based generalisation oracle,
- and LLM-proposed auxiliary lemmas validated by a sub-supercompilation pass.

The system is mechanised in Rocq with no admitted lemmas and proves a range of equational properties automatically via symbolic execution. These include monad laws, insertion sort correctness, reverse-append distribution, and additional ω-rule examples. :contentReference[oaicite:0]{index=0}

The key claim is that the sequent-calculus perspective is not merely explanatory but directly guides the design of new supercompilation techniques.

---

## 🧠 Strengths

### 1. Clear and compelling conceptual contribution

The identification of:
- generalisation ≡ cut introduction,
- speculation ≡ variable projection,
- strengthened induction ≡ ω-rule,

is elegant and insightful. The framing is not just retrospective: it directly informs the design of the system.

This is a strong conceptual contribution that unifies several strands of prior work.

---

### 2. Mechanisation as a design tool

A notable strength is that the mechanisation is not merely used for verification, but actively *drives the discovery of missing components* in the theory.

The identification of:
- the inability of anti-unification to drop variables,
- the need for auxiliary lemmas in cyclic proofs,

emerges naturally from the formalisation.

This supports the paper’s central methodological claim.

---

### 3. Principled integration of LLMs

The use of LLMs for:
- generalisation (cut proposals),
- lemma synthesis (ω-rule),

is carefully structured so that:
- the LLM is not trusted for soundness,
- all outputs are validated by the kernel via the SC pipeline.

This “oracle + kernel validation” design is clean and convincing.

---

### 4. Strong motivating examples

The reverse-append example is particularly compelling:

- standard SC fails to fuse the terms,
- the LLM proposes a non-trivial auxiliary lemma,
- the sub-SC validates it,
- the main SC uses it to complete the proof.

The inclusion of a proof graph explaining how the lemma enables the cyclic backlink is especially helpful. :contentReference[oaicite:1]{index=1}

This example clearly demonstrates the benefit of the proposed approach.

---

### 5. Non-trivial automation results

The system proves:
- monad laws,
- insertion sort correctness,
- reverse-append distribution,
- `sorted (sort l) = true`,
- and other ω-rule examples,

entirely automatically via `vm_compute`.

This is a substantial demonstration of capability.

---

### 6. Thoughtful evaluation of LLM behaviour

The scrambling experiment (renaming all identifiers) is a strong attempt to address concerns about memorisation. The results suggest that the LLM relies on structural information rather than names alone. :contentReference[oaicite:2]{index=2}

This strengthens the credibility of the approach.

---

## ⚠️ Weaknesses

### 1. Lemma synthesis loop not fully integrated

The paper explicitly states that:
> the lemma is hand-provided in the Rocq tests, and wiring the LLM loop remains

This is the main weakness.

While all components of the ω-rule pipeline are present and demonstrated, the lack of full integration weakens the claim of end-to-end automation.

---

### 2. Limited quantitative evaluation

The evaluation is primarily:
- example-driven,
- qualitative,
- and focused on correctness.

Missing aspects include:
- performance (search cost, oracle calls),
- failure cases,
- scalability to larger programs.

While this is not uncommon for ICFP, a slightly broader evaluation would strengthen the paper.

---

### 3. Relationship to prior HLS systems could be clearer

The paper positions itself relative to higher-level supercompilation, but the comparison is mostly conceptual.

It would be helpful to clarify:
- what transformations are enabled here that are not handled by prior HLS systems,
- whether the LLM oracle subsumes or complements existing heuristics.

---

### 4. Remaining limitations are significant

The paper acknowledges that:
- conditional lemmas are not yet supported,
- commutativity is still unprovable,
- lemma environments are not fully developed.

These are reasonable future directions, but they highlight that the system is not yet complete.

---

## ❓ Questions for the Authors

1. How often does the LLM fail to propose a useful lemma in practice?
2. What are typical failure modes of the system?
3. How expensive are sub-SC lemma validation runs?
4. How sensitive is the system to prompt design or model choice?
5. Can the authors compare their approach empirically with existing HLS systems?

---

## 📊 Overall Evaluation

| Criterion          | Score |
|-------------------|------|
| Originality       | 5 (Excellent) |
| Technical Quality | 4 (Very Good) |
| Clarity           | 4 (Very Good) |
| Significance      | 5 (Excellent) |
| Evaluation        | 3 (Good) |

---

## 🧾 Confidence

**High**

The paper is clearly written, technically detailed, and presents a coherent and plausible system. The contributions are understandable and well-supported by examples.

---

## 🏁 Recommendation

**Weak Accept**

---

## 🧠 Summary of Recommendation

This paper presents a compelling integration of:
- proof-theoretic insight,
- mechanised reasoning,
- and LLM-guided synthesis.

The key idea—that supercompilation generalisation corresponds to cut introduction, and that this naturally leads to an oracle-based architecture—is both elegant and impactful.

The system demonstrates real capability, particularly in handling examples that standard supercompilation cannot.

The main weakness is that the ω-rule lemma synthesis loop is not yet fully integrated, leaving a small gap between the conceptual design and the implemented system.

Overall, the contribution is strong and timely, and I recommend acceptance.
