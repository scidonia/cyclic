# Cyclic normalization + unfold-control plan

This note records the overarching idea for this repo, and then the concrete plan for how we control/automate the well-foundedness obligations that make the approach terminate.

## 0. Overarching idea (pipeline)

We start from a CIC-style term language with dependent types and a `fix` construct.

Key point: `fix` induces *back-links* in the sense that unfolding a `fix` takes you back to (a renamed/substituted instance of) the same definition. So a term can be viewed as a **finite object that implies potentially infinite unfolding behaviour**.

The intended pipeline is:

1. **Read off a term into a cyclic pre-proof**
   - Input: a term `t` (and its typing/equality goal).
   - Output: a **cyclic pre-proof graph** whose nodes are judgements and whose edges represent rule-premises.
   - Back-links in the proof graph arise from `fix`/unfold rules: they introduce edges that “jump back” to earlier obligations.
   - At this stage it is only a *pre-proof*: we have not yet established that the cyclic structure is globally sound or that any induced normalization procedure terminates.

2. **Normalize / reduce the cyclic pre-proof (valid cyclic reduction)**
   - We define a reduction relation on cyclic pre-proofs (or on cyclic proofs once progress is established).
   - This reduction is *not* ordinary object-language evaluation. It is a proof-level normalization that can:
     - unfold back-links (expand a `fix`-implied edge)
     - create new back-links (folding/refolding to keep the object finite)
     - normalize partial computations that appear inside proof obligations (e.g. case-of-constructor, β-like steps, etc.)
   - This is the key “unusual reduction”: it operates on the cyclic proof object, not directly on terms.

3. **Stop at a cyclic normal form**
   - The goal is to reach a normal form of the cyclic proof object (or a stable representative), where further proof-level normalization would only repeat structure.

4. **Read back to the term calculus**
   - From the cyclic normal form, reconstruct a CIC-style term (with `fix`), potentially with **new cycles/back-links**.
   - Intuition: we “tie the knot” in a controlled way and synthesize a finite `fix` term representing the stabilized cyclic structure.

5. **Correctness goal (at term level)**
   - Ultimately we want a theorem stating that the reconstructed term is equivalent to the original term under a robust semantic/program equivalence (likely contextual equivalence, proved via a logical relation).
   - We can either:
     - prove intermediate equivalences at the cyclic-proof level (bisimulation-style), then transport them through readback, or
     - delay the equivalence statement until after readback and prove the end-to-end theorem on CIC terms.

## 1. What must be controlled (why “progress” is not just evaluation)

The normalization/reduction phase above must be carefully controlled.

If we allow arbitrary proof-level computation (unfolding `fix` everywhere, β-reducing everywhere, etc.), the normalization procedure itself will not terminate, and proof graphs can blow up.

So we need an **unfold-control discipline** that ensures:
- proof-level normalization terminates (or reaches a stable normal form), and
- back-link creation is justified (does not introduce unsound cyclic reasoning).

This is where we need a **well-founded relation** / measure to justify each normalization step.

Crucially: this well-foundedness is about *the proof normalization algorithm*, not about the object-language small-step semantics.

## 2. Unfold-control: candidate well-founded relations

A naïve approach would use a syntactic **subterm** ordering (or term size) to justify unfolding, but that is often too weak or too syntactic for cyclic proof normalization.

Instead, the guiding idea is to control normalization using orderings that capture “information content” or “structural embedding” of obligations.

Candidate control relations (not mutually exclusive):

- **Graph homomorphism / embedding**
  - Compare proof graphs (or local subgraphs/SCC summaries) by existence of a homomorphism.
  - Intuition: a new obligation/state is not genuinely new if it embeds into a previous one.

- **Simulation relation**
  - Use a simulation/preorder between states/obligations: one state simulates another if it is at least as informative and has no more behaviour.
  - Useful when normalization steps “refine” a state but do not strictly shrink syntax.

- **Constraint weakening**
  - When judgements carry constraints (e.g. equalities, typing side-conditions, environments), define an ordering where weakening constraints counts as progress toward stabilization.
  - This matches the idea that normalization can introduce constraints, then later weaken/solve them.

- **Information ordering**
  - A general semantic preorder: state `s'` is below `s` if `s'` contains no more information than `s` (or is more abstract).
  - This can support termination by preventing infinite strictly-increasing chains of information.

- **Homeomorphic embedding (possible tool, not the only one)**
  - Classic termination control for symbolic evaluation/supercompilation.
  - If a state embeds into a prior state, we stop unfolding and introduce a back-link.
  - This is especially plausible if our normalization resembles a partial evaluator.

The plan is to implement unfold-control in a way that is parameterized by such a relation, so we can experiment.

## 3. Progress obligations: what we must prove about cycles

We still need a global condition that makes cyclic objects sound.

The repo’s current progress infrastructure is ranking-based (see `theories/Progress/Ranking.v`), but conceptually we want:

- A predicate `ProgressOK p` on cyclic pre-proofs/proofs `p`.
- `ProgressOK p` should imply that cyclic reasoning is globally sound (no “bad” cycles).

For the normalization story, it’s useful to phrase obligations as:

- **(CycleProgress)** every directed cycle contains at least one designated “progress event”.

But here “progress event” should be interpreted as:
- a normalization step / back-link justification step that is decreasing under the unfold-control relation,
not “object-language evaluation took a step”.

## 4. Witness type: unfold-control / measure packages

We want a single witness type that can represent multiple unfold-control strategies.

A witness package should include:
- a domain `M` and preorder/strict order (or other well-founded structure)
- a ranking/summary function from states/obligations to `M`
- proofs that normalization steps do not increase (and sometimes strictly decrease) this measure
- a proof that every cycle contains a strict descent (or a progress event)

In code, this is aligned with the existing pattern:
- `theories/CyclicProof/CyclicProof.v` abstracts a witness type `W` and a predicate `progress_ok`.
- `theories/CyclicProof/Ranked.v` specializes `W` to a ranking witness and `progress_ok` to `Ranking.ranking_condition`.

## 5. Library of known control measures (automation targets)

We want automation that tries a small library of known control strategies.

Initial library (for early experiments):

1. **Structural recursion**
   - term size / AST size
   - constructor depth
   - bounded unfolding depth on specific constructs

2. **Lexicographic recursion**
   - pairs/tuples of measures (e.g. fuel first, then structural size)

3. **Graph/information-based controls (planned next)**
   - simulation preorders
   - constraint weakening / information ordering
   - embedding/homomorphism checks
   - homeomorphic embedding as a specific instance

4. **User-supplied explicit witness**
   - when automation cannot infer a good control relation

Later extension:
- guarded productivity control (guard events as progress)

## 6. Automation strategy

Given:
- a cyclic pre-proof (built by reading off the term), and
- a declared/provided progress-event predicate (derived from normalization/unfold-control),

Automation should:
1. generate obligations for the chosen global condition (ranking/cycle progress)
2. try known control measures in a priority order
3. discharge monotonicity/strictness/cycle obligations using lemmas about the chosen measure
4. leave any remaining obligations explicit

## 7. Concrete next steps in the repo

1. Define typed homeomorphic embedding on judgements (unfold control).
2. Define the *read-off* function/relator from CIC terms to cyclic pre-proofs.
3. Define the cyclic normalization/reduction relation (unfold/fold + partial computation normalization).
4. Define readback from cyclic normal form to CIC terms (with `fix`).
5. Use embedding to justify back-links (stop/unfold criterion).
6. Add one information-ordering style control (simulation/constraint weakening/homomorphism).
7. Prove termination/stability of normalization under the chosen control.
8. State the end-to-end correctness theorem at term level (likely via a logical relation; contextual equivalence as a corollary).
