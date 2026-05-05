# Logical Relations Extension — Architecture Plan

## The Goal

Prove statements of the form:

    ∀ l : List.  sorted (sort l) ⇓ true
    ∀ m n : Nat. plus m n = plus n m

These are **universal convergence statements**, not CIU equivalences.
They require a semantic notion that the current framework lacks:
**refinement typing** — a term converging to a value satisfying a predicate.

## What Already Exists

### `ciu` (CIU.v)
```
ciu t u  ≡  ∀ σ v.  t[σ] ⇓ v  ↔  u[σ] ⇓ v
```
Equivalence of two terms under all substitutions.

### `ciu_jTy` (CIUJudgement.v)
```
ciu_jTy Σ Γ t u A  ≡  ∀ σ : has_subst Σ Γ, ∀ v.  t[σ] ⇓ v  ↔  u[σ] ⇓ v
```
Same, restricted to typed closing substitutions.

### `ciu_jTy_rel` (CIUJudgement.v)
```
ciu_jTy_rel Σ Γ t u A R  ≡  ∀ σ v.  t[σ] ⇓ v  →  ∃ v'. u[σ] ⇓ v' ∧ R v v'
```
Relational version — values compared up to R, not syntactic equality.
**This is the seed of logical relations. It already exists.**

### `supercompile_ciu_soundness_untyped`
```
sc_jTy_tc fuel Σ Γ t A = Some (v, b)  →  ciu t (residualise b v)
```
The main SC soundness theorem. Hypothesis: only `trace_condition_ok`.

## The Missing Piece: Adequacy

What we need for `sorted (sort l) = true` is not equivalence between two
terms — it is **adequacy**: a single term converges to a specific value.

    adequate P t  ≡  ∀ σ : has_subst Σ Γ.  ∃ v.  t[σ] ⇓ v  ∧  P v

where `P : tm → Prop` is a predicate on values.  For our use case:
    P = (fun v => v = bool_true)   or   P = (fun v => v = zero ∨ ∃ n. v = succ n)

This is **not** CIU between two terms.  It is the statement that `t`
always converges and its value satisfies `P`.

## Logical Relations: The Right Framework

Define a **step-indexed logical relation** `⟦A⟧` by induction on type `A`:

```
⟦Bool⟧   = { v | v = true ∨ v = false }         -- all Bool values
⟦Nat⟧    = { v | ∃ n. v = ⌈n⌉ }                 -- all Nat values  
⟦List⟧   = { v | v = nil ∨ ∃ x xs. v = cons x xs ∧ x ∈ ⟦Nat⟧ ∧ xs ∈ ⟦List⟧ }
⟦A → B⟧  = { t | ∀ u ∈ ⟦A⟧. tu ↓ ∧ ∀ v. tu ⇓ v → v ∈ ⟦B⟧ }
```

**Fundamental lemma**: `Γ ⊢ t : A  →  t ∈ ⟦A⟧` (all well-typed terms are adequate).

**Refinement**: for a predicate `P : tm → Prop`,
```
⟦{x : A | P x}⟧ = { t | t ∈ ⟦A⟧ ∧ ∀ v. t ⇓ v → P v }
```

The statement `sorted (sort l) = true` becomes:
```
sort ∈ ⟦{f : List → List | ∀ l. sorted (f l) ⇓ true}⟧
```

## Connection to `ciu_jTy_rel`

`ciu_jTy_rel` with `R = (fun v _ => v ∈ ⟦A⟧)` gives adequacy:
```
ciu_jTy_rel Σ Γ t t A (fun v _ => P v)
  ≡  ∀ σ v.  t[σ] ⇓ v  →  P v
```
This is exactly adequacy for `t` under typed substitutions.

**The bridge**: `ciu_jTy_rel` is already the right notion;
we just need to instantiate it with the logical relation `⟦A⟧` as `R`.

## The SC Extension: Conditional Soundness

The current soundness theorem:
```
sc_jTy_tc fuel Σ Γ t A = Some (v, b)
  →  ciu t (residualise b v)
```

The extension needed:
```
∀ (l, r) ∈ lemmas.  ciu l r    (* lemmas are proved *)
  →  sc_jTy_tc_with_lemmas fuel Σ lemmas Γ t A = Some (v, b)
  →  ciu t (residualise b v)
```

For refinement goals, we additionally need:
```
∀ (l, r) ∈ lemmas.  l ∈ ⟦A_l⟧    (* lemmas are adequate *)
  →  sc_refine fuel Σ lemmas Γ t A P = Some (v, b)
  →  t ∈ ⟦{x : A | P x}⟧
```

where `sc_refine` is the SC that also uses lemmas as rewrite rules and
checks that all base cases satisfy `P`.

## Implementation Plan

### Phase 0 (now): Sketch the logical relation in Rocq

Define `lr_val : ty_sem → tm → Prop` by induction on a semantic type:

```coq
Inductive ty_sem : Type :=
| ty_nat  : ty_sem
| ty_bool : ty_sem
| ty_list : ty_sem
| ty_arr  : ty_sem → ty_sem → ty_sem
| ty_ref  : ty_sem → (tm → Prop) → ty_sem.   (* refinement *)

Fixpoint lr_val (T : ty_sem) (v : tm) : Prop :=
  match T with
  | ty_nat       => ∃ n : nat, v = nat_tm n
  | ty_bool      => v = bool_true ∨ v = bool_false
  | ty_list      => lr_list v
  | ty_arr A B   => ∀ u, lr_val A u → ∃ w, terminates_to (tApp v u) w ∧ lr_val B w
  | ty_ref A P   => lr_val A v ∧ P v
  end

with lr_list (v : tm) : Prop :=
  v = nil ∨ ∃ x xs, v = cons x xs ∧ lr_val ty_nat x ∧ lr_list xs.
```

**Adequate term**: `lr_tm T t  ≡  ∃ v. terminates_to t v ∧ lr_val T v`

### Phase 1: Fundamental lemma

```coq
Theorem lr_fundamental :
  ∀ Σ Γ t A,
    has_type Σ Γ t A →   (* typing *)
    lr_env Γ σ →          (* σ is lr-adequate for Γ *)
    lr_tm (ty_of A) (t.[σ])
```

This requires `ty_of : ty → ty_sem` to extract a semantic type from a
syntactic type. For our object language this is straightforward since types
are inductive (Nat, List, Bool, arrows).

### Phase 2: Lemma environment

Add `lemma_env : list (tm * tm * ty_sem)` — triples `(lhs, rhs, T)` with
evidence `lr_tm T lhs` (the lemma is adequate at type T).

During driving: when a configuration matches `lhs`, rewrite to `rhs`.
This is sound because `lr_tm T lhs → lr_tm T rhs` follows from the lemma
and the fundamental lemma for `rhs`.

### Phase 3: SC with refinement goals

```coq
Definition sc_refine
    (fuel : nat) (Σ : env) (lemmas : lemma_env)
    (Γ : ctx) (t : tm) (T : ty_sem) (P : tm → Prop)
    : option (nat * cfg_builder)
```

Returns a cfg_builder that, when residualised and checked, witnesses
`lr_tm (ty_ref T P) t`.

### Phase 4: Soundness theorem

```coq
Theorem sc_refine_sound :
  ∀ fuel Σ lemmas Γ t T P v b,
    lemmas_adequate lemmas →
    sc_refine fuel Σ lemmas Γ t T P = Some (v, b) →
    trace_condition_ok b = true →
    lr_tm (ty_ref T P) t
```

i.e.: if the SC with lemmas succeeds and the graph is well-founded,
then `t` converges to a value satisfying `P`.

## Examples That Become Provable

Once Phase 1-4 are complete:

| Statement | Lemma needed | Discovered by |
|---|---|---|
| `∀ l. sorted (sort l) ⇓ true` | `sorted l → sorted (insert x l)` | LLM |
| `∀ m n. plus m n = plus n m` | `plus 0 n = n`, `plus (S m) n = S (plus m n)` | SC alone |
| `∀ l. sort (sort l) = sort l` | sort is idempotent on sorted lists | LLM |
| `∀ l x. member x (sort l) = member x l` | sort preserves membership | LLM + SC |

## Relationship to `ciu_jTy_rel`

The existing `ciu_jTy_rel` is the special case where:
- The logical relation `R` is chosen as `(fun v _ => lr_val T v)`
- The two terms `t` and `u` are the same (`t = u`)
- This gives adequacy: `∀ σ v. t[σ] ⇓ v → lr_val T v`

So `ciu_jTy_rel` is NOT a new concept — it is already logical relations,
just not yet connected to the inductive definition of `lr_val`.

The bridge lemma:
```coq
Lemma lr_implies_ciu_rel :
  lr_tm T t →
  ciu_jTy_rel Σ Γ t t A (fun v _ => lr_val T v)
```

## Key Design Decisions

1. **Step-indexing vs. size-indexing**: For our pure CBN language without
   general recursion in the type system, step-indexing is not strictly
   necessary. The logical relation can be defined by induction on the type
   structure alone. Step-indexing is needed for languages with recursive
   types or effects.

2. **Unary vs. binary**: A unary logical relation (adequacy, `lr_val T v`)
   is simpler than a binary one (equivalence). We want unary because our
   goal is to prove `P(t) = true`, not `t = u`. The existing `ciu_jTy_rel`
   is binary; we need to add the unary fragment.

3. **Integration with SC**: The SC currently produces CIU (binary). The
   extension produces adequacy (unary) when the goal is a refinement type.
   Both should use the same cfg_builder infrastructure.

4. **`Parameter` discipline**: The lemma environment has the same trust
   structure as the LLM oracle: `lemmas_adequate` is a hypothesis, not
   an axiom. If the sub-SC fails to prove a lemma, it is not added.

## Connection to the ω-Rule

The logical relation `lr_val ty_list` is exactly the ω-rule for lists:
```
lr_list nil                                  (base case)
lr_list (cons x xs)  ←  lr_nat x ∧ lr_list xs   (step case)
────────────────────────────────────────────────
∀ v : List.  lr_list v                          (ω-rule)
```

The fundamental lemma IS the ω-rule: it says all well-typed list terms
converge to values satisfying the inductive predicate.

The SC with the lemma environment then applies this to the specific
predicate `sorted`, proving `sorted (sort l) = true` by:
1. Fundamental lemma: `sort l ∈ ⟦List⟧` (sort produces a list)
2. Lemma: `sorted l → sorted (insert x l)` (proved by SC, induction on l)
3. Refinement: `sort l ∈ ⟦{xs : List | sorted xs = true}⟧` (sort produces sorted)

Step 3 is the new thing. Steps 1 and 2 are already within reach.
