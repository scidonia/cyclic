# Type Theorist Qualms & Responses

Correspondence with James Brotherston and self-review of the ESOP 2027 paper
"Supercompilation as Cyclic Proof Search for the Calculus of Constructions."

---

## Qualm 1: Where is the focusing judgment?

**Concern:** The paper calls this a "focused cyclic sequent calculus" but doesn't define proper focusing judgments with polarity assignments and phase transitions (Andreoli, Liang-Miller). Is there a theorem that driving rules *are* invertible and splitting rules *are* not?

**Status:** Addressed.

- The paper now explicitly states we use "focusing" in the **operational sense** — invertible rules applied eagerly, non-invertible rules at choice points — without explicit polarity judgments or phase transitions.
- Invertibility of driving rules is proved: `step_ciu` (CIU.v:27) shows each CBN step preserves CIU equivalence in both directions.
- Non-invertibility of splitting is argued by counterexample: committing to a single branch (e.g. nil) produces a residual that is not CIU-equivalent to the source.
- The completeness theorem (focused strategy doesn't lose provability) is explicitly deferred as future work.

---

## Qualm 2: What happens with dependent elimination motives?

**Concern:** The Vec example requires a dependent motive — the return type differs between the nil and cons branches. A proper focused calculus needs to explain how the motive is propagated through the async phase. Does driving normalise the motive? Is that normalisation proved to terminate?

**Status:** Partially addressed.

- The paper's "Post-hoc induction" section (§1.4) explains that driving normalises the index during search, and when a fold-back is discovered, the index equality is already reduced to definitional form.
- The budget-trace construction ensures termination of the normalisation process.
- A formal treatment of motive propagation through the focused phases is not yet mechanised — this is noted under "Limitations" (deferred CIC features).

---

## Qualm 3: Budget trace — admissibility or coincidence?

**Concern:** The budget-instrumented trace graph yields a ranking, but is this a *proof-theoretic* result or an *operational* one? Does it correspond to an admissible rule in the sequent calculus, or is it specific to this graph algorithm?

**Status:** Addressed.

- The paper now presents the budget trace as a **combinatorial proof** that the lifted graph is acyclic when the trace check passes (§6.2).
- The ranking is derived from the acyclicity of the lifted graph, which is a proof-theoretic property (well-founded induction).
- The result is specific to this SC implementation, but the method (budget instrumentation + cycle detection) is general.

---

## Qualm 4: Substitution and the backlink rule

**Concern:** The `back` rule takes a substitution as a premise and produces the companion as conclusion. Treating substitutions as *premises* to an inference rule makes the calculus depend on an external notion of substitution checking. Is the `back` rule admissible?

**Status:** Addressed.

- The paper now explicitly labels the substitution as a premise in the back rule (Fig 2).
- The CIU soundness proof (Claim 3) establishes that the backlink is justified: when a vertex's goal is an instance of a previous vertex's companion under a substitution, the residual of the companion applied to the substitution is CIU-equivalent to the backlink's goal.
- Admissibility (that any backlink-closed proof could be rewritten as a proof without backlinks) is not claimed and follows from Brotherston-Simpson's correspondence theorem for first-order logic, which is not yet extended to CoC with inductives.

---

## Qualm 5: "Post-hoc induction" — formal claim?

**Concern:** The paper says induction principles are "discovered post-hoc from the cycle structure." Is there a theorem that every cyclic proof *corresponds to* a standard proof with an explicit induction rule? Brotherston-Simpson (2011) have such a theorem for first-order logic — is there an analogue for CoC with inductives?

**Status:** Acknowledged, not proved.

- The paper states this as an **interpretation**, not a formal theorem.
- The cyclic proof structure *operationally* discovers the induction scheme, but we do not prove a correspondence theorem between cyclic proofs and standard induction proofs.
- This is a natural extension of Brotherston-Simpson's result, deferred to future work.

---

## Qualm 6: Novelty boundaries

**Concern:** What is genuinely new vs explanatory reframing? Is the primary contribution (a) a new calculus, (b) a new correctness proof architecture, (c) a mechanised synthesis, or (d) a conceptual reinterpretation?

**Status:** Sharpened.

- The paper now explicitly claims: first to **combine** focusing, cyclic proof, and SC in a dependently typed setting (§1).
- Comparison with Krustev (first Coq verification of SC, but first-order) and Jones-Hamilton (bisimulation correctness, but not cyclic proof-theoretic).
- The novel contribution is (b) + (c): a mechanised CIU correctness proof for SC in CoC with inductives, using cyclic proof theory as the organisational principle.

---

## Qualm 7: Can supercompilation diverge? Does completion guarantee a failure?

**Concern:** The correspondence is directional: every successful (terminating with trace_condition_ok) SC run yields a valid cyclic proof. But potentially non-terminating input programs may yield pre-proofs that fail the trace condition. Supercompilation *can* loop.

**Status:** Addressed.

- The paper now explicitly states the directionality in the introduction: "every successful supercompilation run yields a valid cyclic proof; the converse does not hold."
- The trace condition (§2.3) detects non-terminating cycles: a pre-proof with a non-progressing cycle fails the check, and `supercompile_jTy_tc` returns `None`.
- The SC loop is fuel-bounded, so it cannot diverge — it either terminates with a pre-proof (which may or may not pass the trace check) or exhausts fuel.
