
# 📄 ICFP Review: *Mechanisation Guides Design: Higher-Level Supercompilation via Sequent Calculus*

---

## ⭐ Summary

This paper presents a mechanised account of higher-level supercompilation (HLS) grounded in a sequent-calculus interpretation of supercompilation as cyclic proof search. Building on prior work, the authors identify three gaps in standard supercompilation:

1. Generalisation as **cut introduction**  
2. Speculation as **variable projection**  
3. Strengthened induction via the **ω-rule**

They implement a four-layer generalisation pipeline:

- Anti-unification (standard SC)  
- Speculation (dependency-based projection)  
- LLM-based generalisation oracle  
- LLM-proposed auxiliary lemmas (ω-rule), validated via sub-supercompilation  

The system is mechanised in Rocq (with no admitted lemmas), and automatically proves a range of equational properties via symbolic execution (`vm_compute`). These include monad laws, insertion sort correctness, reverse-append distribution, and others.

The central claim is that the **sequent-calculus perspective is not just explanatory but a design tool**, directly leading to new system capabilities.

---

## 🧠 Strengths

### 1. Strong conceptual unification

The correspondence:
- supercompilation generalisation ↔ cut introduction  
- failure of cyclic induction ↔ need for ω-rule  

is elegant and insightful. This framing clarifies long-standing intuitions in the supercompilation literature and provides a principled way to extend the technique.

This is the paper’s strongest contribution.

---

### 2. Mechanisation that drives design (not just validation)

Unlike many mechanisation papers, the formalisation here actively *guides* system design. The identification of gaps (e.g. inability to drop variables, inability to strengthen induction) emerges directly from the formal account.

This is a compelling example of mechanisation as a **design methodology**, not just a correctness tool.

---

### 3. Clean soundness story with LLM integration

The use of an LLM as an oracle for:
- generalisation (cut proposals)
- lemma synthesis (ω-rule)

is carefully structured so that:
- the LLM is **not trusted for soundness**
- all results are validated via the existing kernel (trace condition / SC pipeline)

This is a strong and principled approach to integrating LLMs into formal systems.

---

### 4. Non-trivial examples

The system proves a range of properties automatically, including:

- Monad laws (List, Maybe)  
- Insertion sort correctness  
- `reverse (append xs ys)` distribution  
- `sorted (sort l) = true` (via ω-rule)  

The reverse-append example is particularly compelling:
- standard SC fails
- the system discovers a non-trivial auxiliary lemma
- validates it
- and completes the proof

This demonstrates genuine added capability.

---

### 5. Thoughtful evaluation of LLM behaviour

The scrambling experiment (renaming all identifiers) is a strong attempt to address the concern that the LLM is merely memorising known patterns. The results suggest that structure, not naming, drives success.

This is a valuable addition and strengthens the paper’s credibility.

---

## ⚠️ Weaknesses

### 1. Lemma synthesis pipeline not fully integrated

The paper states that:
> the lemma statement is hand-provided in the Rocq tests, and wiring the LLM loop remains

This is a significant gap between the *conceptual architecture* and the *fully implemented system*.

While the components are all present, the lack of end-to-end integration weakens the claim that the system fully automates ω-rule reasoning.

---

### 2. Limited comparison to prior HLS work

The paper positions itself relative to higher-level supercompilation (HLS), but the comparison remains somewhat high-level.

In particular:
- How does this approach differ operationally from existing HLS systems (e.g. Supero)?
- What transformations are now possible that were not before, beyond the provided examples?

A more concrete comparison would strengthen the contribution.

---

### 3. Evaluation is qualitative rather than systematic

The evaluation consists of:
- a collection of example theorems
- a small LLM robustness experiment

Missing elements include:
- failure cases
- performance characteristics (e.g. search cost, oracle calls)
- sensitivity to prompt design

While this is acceptable for ICFP, a slightly broader evaluation would improve confidence.

---

### 4. LLM dependence remains heuristic

Although soundness is preserved, the system’s effectiveness depends on:
- the quality of LLM proposals
- prompt engineering

This is acknowledged, but the paper could better characterise:
- when the LLM fails
- how often fallback mechanisms succeed

---

## ❓ Questions for the Authors

1. How often does the LLM fail to propose a useful lemma in practice?
2. Can the authors provide examples where the system still fails, even with the ω-rule?
3. How sensitive is the system to prompt design or model choice?
4. How does this approach compare empirically to existing HLS systems?
5. What is the expected overhead of the lemma-validation sub-SC runs?

---

## 📊 Overall Evaluation

| Criterion              | Score |
|-----------------------|------|
| Originality           | 5 (Excellent) |
| Technical Quality     | 4 (Very Good) |
| Clarity               | 4 (Very Good) |
| Significance          | 5 (Excellent) |
| Evaluation            | 3 (Good) |

---

## 🧾 Confidence

**High**

The paper is clearly written, technically detailed, and presents a coherent story. The contributions are understandable and plausibly correct, though some implementation details (especially around the ω-rule loop) could be clarified further.

---

## 🏁 Recommendation

**Accept (weak accept → accept)**

---

## 🧠 Summary of Recommendation

This paper presents a compelling and well-executed integration of:
- proof-theoretic insight
- mechanised reasoning
- and LLM-guided synthesis

The key idea—that supercompilation generalisation is cut introduction, and that this naturally leads to an oracle-based architecture—is both elegant and impactful.

While the implementation is not entirely complete (notably the lemma synthesis loop), the conceptual contribution and supporting evidence are strong enough to merit acceptance.

With minor strengthening—particularly around integration and evaluation—this could become a highly influential paper.
