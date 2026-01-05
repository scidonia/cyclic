# Cyclic proof isomorphism plan (read-off + extract)

This note specifies the *first concrete milestone*:

- implement **read-off/compile** from CIC terms to cyclic proofs (graph object)
- implement **extraction/readback** from cyclic proofs back to CIC terms
- prove these form an isomorphism (up to the right notion of equality)

The key requirement for this milestone:
- **no `tFix` occurs anywhere inside the cyclic proof object** (neither in terms nor in types)
- all recursion (including recursive types, if any) is represented only by **proof cycles/back-links** plus an explicit **typed substitution** judgement (`jSub`)

## 0. Target representations

### 0.1 Source language

- CIC-style term syntax: `theories/Syntax/Term.v` (`Syntax.tm`)
- includes `tFix` as the source recursion construct

### 0.2 Cyclic proof object (graph)

We represent the compiled artifact as a *rooted finite digraph* whose nodes are labelled by cyclic judgements.

We use the generic graph infrastructure:
- `theories/Graph/FiniteDigraph.v`
- `theories/Preproof/Preproof.v`

A cyclic proof is later a `Preproof.preproof` plus a global progress witness.
For this milestone we focus on producing a **rooted preproof** (local correctness only).

## 1. Judgement language for read-off (vertex-based, fix-free)

We introduce a dedicated cyclic judgement language which mirrors typing rules but **never stores `tFix` anywhere**, including inside types.

Everything that used to be a `tm` becomes a **vertex** in a shared, possibly-cyclic term graph:
- terms are vertices
- types are vertices
- explicit substitutions are also represented by vertices (see below)

Practically: any recursion that would have been written using `tFix` (whether at term level or type level) must instead be represented by a **cycle in the proof graph**, mediated by back-links and explicit substitutions (`jSub`).

Core idea:
- judgements talk about **graph vertices** (not terms)
- rule instances are determined by node labels + outgoing edges

### 1.1 Node labels (introduction schemas)

Each vertex has a *schema label* corresponding to an introduction form:

- `Var x` (allowed)
- `Sort i`
- `Pi`, `Lam`, `App`
- `Ind`, `Roll`, `Case`
- `Subst` (explicit substitution object; evidence node)
- `BackLink` (use schema)

There is **no fixpoint binder schema** (`jFix`/`FixBinder`) at all.

Recursion is represented purely by:
- introducing a cycle target vertex (an ordinary vertex whose label is one of the non-`tFix` constructors), and
- using `BackLink` nodes that jump to that target.

Crucially, every back-link carries explicit *evidence* of instantiation:
- a back-link node points to a dedicated `Subst` vertex that encodes the substitution.

No schema label contains `tFix`, and neither do any types represented by vertices.

**Concrete choice (for next implementation step):** represent a substitution as a linked list of `Subst`-vertices.

- `SubstNil k` where `succ(sv) = []`
- `SubstCons k` where `succ(sv) = [u; sv_tail]`

This matches the existing list-backed substitution checking rule (`has_subst`) but makes the *tail substitution* explicit as a vertex, which is necessary for the `jSubV` rule to mirror `Typing.Cyclic.rule`.

A back-link node then needs only:
- `succ(back) = [target; sv]`

Intuition: this is the vertex analogue of `Typing.sub = (k, list tm)`.

### 1.2 Typing/equality/substitution judgements over vertices

We use a typing judgement of the form:

- `jTyV Γ v A` meaning: “vertex `v` denotes a term of type vertex `A` under context `Γ`”

We include definitional-ish equality (invariant under vertex renaming):

- `jEqV Γ v w A` meaning: “vertices `v` and `w` are equal at type vertex `A` under Γ”

And we represent explicit substitutions as first-class vertices:

- `jSubV Δ sv Γ` meaning: “substitution vertex `sv` is a typed substitution from Γ into Δ”

The point of `jSubV` is to represent recursive calls using *explicit* typed substitutions (encoded by `Subst` vertices) rather than `tFix` terms.

## 2. Rule relation (mirrors the CIC typing rules)

Define `ruleV` on vertex-typing judgements so that each introduction schema mirrors the corresponding CIC rule.

### 2.1 Ordinary introduction rules

For each schema label, the premises are the same shape as in `Typing.has_type`:

- `Var`: premise-free, uses context lookup
- `Sort`: premise-free
- `Pi`: premises for domain/codomain formation
- `Lam`: premises for type formation + body typing
- `App`: premises for function typing + argument typing
- `Ind/Roll/Case`: same premises as existing `Typing` rules

These premises refer to other vertices via `jTyV`.

### 2.2 Recursion without `tFix`: cycles + backlink via `jSubV`

There is **no fixpoint introduction rule** and no fixpoint binder schema.

Instead, recursion is represented purely by **graph cycles**:

- pick a *cycle target vertex* `u` whose label is an ordinary constructor schema (e.g. `Lam`, `Pi`, `Case`, …)
- recursive call sites are compiled as **BackLink** vertices that point back to `u`

Back-links must use an explicit substitution *vertex* as evidence:

- a back-link node has outgoing edges to:
  - the target vertex `u`
  - a substitution vertex `sv` (a linked `Subst` chain)

- the back-link typing rule has premises including:
  - `jTyV Γ0 u A0` (the target obligation)
  - `jSubV Γ sv Γ0` (typedness of the explicit substitution)

and concludes:
- `jTyV Γ backlink (A0[sv])` (apply the explicit substitution encoded by `sv`)

Intuition:
- the cycle target vertex `u` stands for the recursive definition
- the back-link stands for “reuse the same obligation again, instantiated by an explicit substitution”
- the global progress condition will later ensure these cycles are sound

### 2.3 Explicit substitutions (`jSubV`) mirror `has_subst`

We need a `jSubV` rule that enforces typed substitutions *computationally*, similar to `Typing.has_subst` in `theories/Judgement/Typing.v`.

Given a substitution vertex `sv` with `label(sv) = SubstNil k` / `SubstCons k` and `succ(sv) = [u0; u1; ...; u(n-1)]`:

- `jSubV Δ sv Γ` should mean: the substitution maps Γ into Δ.

Rule sketch (structural, list-backed):

- base: if `Γ = []` and `label(sv) = SubstNil k`, then `jSubV Δ sv []` holds.
- step: if `Γ = A :: Γ'` and `label(sv) = SubstCons k` with `succ(sv) = [u; sv_tail]`:
  - premise: `jSubV Δ sv_tail Γ'`
  - premise: `jTyV Δ u (substV sv_tail (shiftV 1 0 A))`

This is exactly the vertex-level analogue of:
- `has_subst Σenv Δ (u :: σ) (A :: Γ)`

where `shiftV` and `substV` are graph-level operations (defined without introducing any `tFix`).

## 3. Read-off compiler (term → rooted preproof)

Implement:

- `read_off : Σenv -> Γ -> t -> A -> rooted_preproof`

The compiler traverses the source term and builds a graph:

- each constructor creates a vertex labelled by its schema
- edges point to compiled subterms

For `tFix A body` (term-level recursion):
- eliminate the `tFix` constructor during compilation
- choose a *cycle target vertex* `u` that will represent the recursive definition
- compile the body (and any types it mentions) using only non-`tFix` schemas
- represent each recursive call site as a `BackLink` vertex pointing to `u` with an explicit substitution `s` (via a `jSub` premise)

For any would-be `tFix` in a type (type-level recursion):
- the same policy applies: `tFix` is eliminated and represented by a cycle in the proof graph
- i.e. recursive types are represented by back-links + substitutions, never by `tFix` syntax

For recursive call sites:
- detect application spines whose head is the recursive variable
- compile them as `BackLink` nodes whose successors include:
  - the cycle target vertex `u`
  - a `Subst` vertex `sv` encoding the argument instantiation
- generate `sv` (a `Subst`-labelled vertex) and ensure there is a `jSubV` proof node/premise establishing that `sv` is well-typed

Local correctness proof obligation:
- show `ruleV` holds at every vertex (by construction)

Global progress is deferred.

## 4. Extraction/readback (rooted preproof → term)

Implement:

- `extract : rooted_preproof -> tm`

Extraction traverses the graph from the root and synthesizes a CIC term.

Key mechanism:
- maintain a map from **cycle target vertices** to fresh `fix` binders/definitions (created once per target)
- when encountering a `BackLink` to target `u` with substitution vertex `sv`:
  - look up the synthesized `fix` for `u`
  - emit a call to that `fix`, instantiated by the explicit substitution encoded by `sv`

Extraction must be invariant under renaming of vertex IDs (only structure matters).

This ensures:
- the cyclic proof contains no `tFix`, but the extracted term does (by synthesis)

## 5. Isomorphism theorems

We want a pair of theorems:

1. **Term round-trip**

- `extract (read_off Σenv Γ t A) = t` (possibly up to definitional equality / α-renaming)

2. **Graph round-trip**

- `read_off Σenv Γ (extract p) A` is equivalent to `p` up to a suitable notion of graph/proof equivalence

The graph equivalence should be at least bisimulation-style (structure-preserving up to renaming of vertices).

## 6. Immediate sub-decisions

Before implementing `read_off` fully, decide:

- exact shape of `BackLink` schema payload:
  - does the node store a pointer to the binder vertex directly, or is that recovered from edges?
- exact representation of the substitution `s`:
  - re-use existing `Typing.sub` (`k` + list), or define a dedicated substitution object for cyclic read-off
- what “equality” is used in the term round-trip theorem:
  - we want **definitional-ish equality**, i.e. equality modulo normalization/computation in the cyclic proof world
  - and equality should be **invariant under vertex renaming** (proofs should not depend on concrete vertex IDs)

For the first milestone, aim for:
- structural equality of extracted terms up to α/renaming,
- and cyclic proof equivalence as bisimulation up to vertex renaming.
