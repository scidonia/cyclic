# Reviewer Checklist (Must-Fix)

This checklist is the action plan to bring `papers/cyclic-sequent-supercomp` up to journal-paper quality, aligned with the stronger style/standard of `papers/cyclic-cic`.

## A. Truthfulness & Scope (Submission Blockers)

- [ ] Add a **Mechanization Status** box/table: what is proved vs admitted vs planned; include Coq file paths and theorem/lemma names.
- [ ] Remove all occurrences of “placeholder” in definitions/theorems; replace with **formal statements**.
- [ ] Fix broken cross-references (e.g. “Section ??”) and undefined labels.
- [ ] Ensure the abstract’s mechanization claims match reality (tone down if proofs incomplete).

## B. Sequent Calculus Completeness / CIC Stubs

- [ ] Decide scope explicitly: full CIC sequent calculus vs sequent system tailored to the SC correspondence; align title/claims accordingly.
- [ ] Provide at least **stubs** for CIC-relevant sequent rules:
  - Π/λ/application in sequent form
  - conversion/definitional equality
  - universes/cumulativity discipline
  - dependent elimination (`case`) obligations (motive + branch typing)
- [ ] Fix the **n-ary constructor split rule** presentation (avoid `TrinaryInfC` for arbitrary constructors).

## C. Technical Precision

- [ ] Clarify operational semantics vs definitional equality: exactly what CBN reduces (and whether it reduces under binders).
- [ ] Define **neutral/stuck** terms used by “split on neutral” and “scrutinee stuck”.
- [ ] Add at least one fully worked correspondence example with explicit:
  - SC node label/config
  - proof node label/sequent
  - successor list/premises
  - local rule instance
  - where the bisimulation mapping is applied

## D. Paper Craft / Structure

- [ ] Add a real **Introduction**: problem, gap, contributions, outline (no “notes/working outline” tone).
- [ ] Replace conclusion with a proper conclusion (summary + limitations + future work), no “this is a working outline”.
- [ ] Add 2–4 figures:
  - SC graph ↔ proof graph mapping diagram
  - example cyclic proof graph (`length(map f l)`) showing progress edge
  - correspondence table (drive/split/fold ↔ rules)

## E. Novelty Claims & Related Work

- [ ] Hedge “first” claims or justify precisely what “supercompilation” means here vs partial evaluation/NbE.
- [ ] Add a short subsection: “What is hard about dependent types here?” (typing preservation during folding, contexts, motives, CIU).

## F. Optional (Nice-to-have)

- [ ] Add algorithm pseudocode for SC + focused proof search.
- [ ] Trim/move the LLM oracle section to future work unless evaluated.
- [ ] Add a small evaluation section (even just mechanized examples + size/steps metrics).
