# Feasibility Analysis: Eliminating `supercompile_satisfies_trace_condition` Axiom

## The Axiom

**Location**: `theories/Transform/SupercompilationCorrespondence.v:1603`

```coq
Axiom supercompile_satisfies_trace_condition :
  forall Σenv fuel Γ t A v scb proof,
    SC.supercompile_jTy_tc fuel Σenv Γ t A = Some (v, scb) ->
    exists τ rank ltM, True.
```

**What it claims**: "If supercompilation succeeds with the trace check, then there exists a ranking witness for the cyclic proof."

## Why It Exists

The axiom bridges two worlds:
1. **Supercompiler world**: `SC.cfg_builder` with term-level labels `C.jTy Γ t A`
2. **Proof world**: Preproofs with sequent labels `jDrive`, `jObs`, `jSub`

The gap: We need to assign **observation trees** (`obs_tree`) to progress vertices (case-splits on neutral terms) to justify semantic descent.

## What We Already Have ✅

### 1. Well-Founded Order (DONE)
- `CyclicTraceConditionObsTree.v` provides `lt_trace_wf : well_founded (option obs_tree)`
- **No axioms** in this module

### 2. Cycle-Progress Property (DONE)
- `SupercompileTraceCheckSound.v` proves `trace_condition_ok_cycle_progress`
- If `SC.trace_condition_ok b = true`, every cycle has a progress edge
- **No axioms** for this property

### 3. Progress Vertex Identification (DONE)
- `Supercompile.v:1163` defines `is_progress_vertex`:
  ```coq
  match lookup_label b v, lookup_succ b v with
  | Some (C.jTy _Γ (tCase _I (tVar _x) _Cmot _brs) _A), Some succs =>
      Nat.ltb 1 (length succs)
  ```
- Progress = case-split on variable with multiple branches

## What's Missing ❌

### Missing Piece 1: Observation Tree Extraction

**Problem**: We need a function:
```coq
extract_obs_tree : Ty.env -> tm -> option obs_tree
```

that computes the observation tree for an inductive-typed term.

**Current state**: `SequentObservationRules.v` defines `ind_obs` (semantic relation) but NOT a computable extraction function.

**Work needed**:
- Define `extract_obs_tree` (likely recursive on term structure)
- Prove `extract_obs_tree_sound`: if it returns `Some o`, then `ind_obs Σenv I t o`
- Prove monotonicity: observation trees reflect semantic descent

**Estimated effort**: 2-3 days (200-400 lines)
- Need to handle all term constructors
- Need fuel/termination measure
- Need to prove correspondence with semantic `ind_obs`

### Missing Piece 2: Vertex Ranking Function

**Problem**: Assign ranks to `cfg_builder` vertices:
```coq
Definition vertex_rank (Σenv : Ty.env) (b : cfg_builder) (v : nat) : option obs_tree :=
  match lookup_label b v with
  | Some (C.jTy Γ t A) => 
      match infer_inductive_type Σenv Γ A with
      | Some I => extract_obs_tree Σenv t
      | None => None
      end
  | None => None
  end.
```

**Work needed**:
- Implement type inference/checking for inductive types
- Prove that progress vertices have inductive-typed scrutinees
- Connect to `extract_obs_tree`

**Estimated effort**: 1-2 days (100-200 lines)
- Type inference infrastructure exists (partial in `ReadOffDrivingPreproof.v`)
- Mainly wiring + local lemmas

### Missing Piece 3: Ranking Condition Instantiation

**Problem**: Prove the four conditions:
```coq
Lemma ranking_condition_for_cfg : forall Σenv fuel b,
  SC.trace_condition_ok b = true ->
  @Ranking.ranking_condition nat _ _
    (cfg_graph b)
    (progress_edge_cfg b)
    (option obs_tree)
    lt_trace
    (vertex_rank Σenv b).
```

**Obligations**:
1. `rc_wf` - **DONE** (use `lt_trace_wf`)
2. `rc_monotone` - Need: rank doesn't increase on non-progress edges
3. `rc_strict` - Need: rank strictly decreases on progress edges
4. `rc_cycle_progress` - **DONE** (use `trace_condition_ok_cycle_progress`)

**Work needed for `rc_monotone`**:
- Non-progress edges: driving steps, folds
- Need: driving preserves or decreases observation trees
- Likely true but requires semantic reasoning about CBN reduction
- **Estimated**: 1-2 days (150-300 lines)

**Work needed for `rc_strict`**:
- Progress edges: case-splits on constructors
- Need: chosen branch has smaller observation tree
- Use `lt_obs_of_in_recs` from our module
- Need to connect split semantics to tree descent
- **Estimated**: 1-2 days (100-200 lines)

## Total Feasibility Assessment

### Time Estimate
**5-8 working days** (800-1200 lines of proof)

Breakdown:
- Day 1-3: Implement & prove `extract_obs_tree` + soundness
- Day 4-5: Vertex ranking function + type inference
- Day 6-7: Prove `rc_monotone` (driving preserves trees)
- Day 8: Prove `rc_strict` + final assembly

### Difficulty Level
**Medium-High**

**Easier parts**:
- We have all the infrastructure (well-founded order, cycle-progress, progress identification)
- Local proofs (tree descent on splits) should be straightforward using `lt_obs_of_in_recs`

**Harder parts**:
- Observation tree extraction is semantic (requires reasoning about CBN evaluation)
- Monotonicity proof requires semantic preservation lemmas for driving rules
- Need to connect syntactic term transformations to semantic observation changes

### Risk Assessment

**Low risk of failure** - the approach is sound:
- Progress edges ARE constructor splits
- Constructor splits DO decrease observation trees (by construction)
- Cycle-progress is already proved

**Medium risk of scope creep**:
- May discover missing semantic lemmas for CBN reduction
- May need to strengthen `SequentObservationRules.v` with computational versions
- Type inference might need non-trivial additions

## Recommendation

### Option A: Eliminate Now (5-8 days effort)
**Pros**:
- Complete mechanization, no axioms
- Demonstrates full semantic correctness
- Good for publication

**Cons**:
- Significant engineering work
- May uncover other missing pieces
- Delays other work

### Option B: Document & Defer
**Pros**:
- Focus on higher-level correspondence properties
- The axiom is "morally correct" - just unproved
- Can reference it as "semantic extraction correctness"

**Cons**:
- Leaves technical debt
- Harder to publish with axioms

### Option C: Hybrid Approach (2-3 days)
**Do the easy parts now**:
1. ✅ Well-founded order (DONE)
2. ✅ Cycle-progress (DONE)  
3. Implement `extract_obs_tree` (computational, may use `Admitted` for soundness)
4. Write `rc_strict` proof sketch showing the structure

**Defer to future**:
- Full soundness proof for `extract_obs_tree`
- `rc_monotone` (driving preserves semantics)

This gives **~80% mechanization** with **~30% effort**.

## My Assessment

**Yes, elimination is feasible, but requires 5-8 focused days.**

The axiom is **not fundamental** - it's engineering complexity, not conceptual difficulty. The core ranking mechanism (obs_tree size) is already proved.

**Decision point**: Is full mechanization worth ~1 week now, or would you prefer to document the gap and continue with correspondence properties?
