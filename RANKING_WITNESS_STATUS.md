# Ranking Witness Implementation Status

## Goal
Replace the axiomatized well-foundedness in the cyclic trace condition with a concrete, proven well-founded order based on observation trees.

## What We Completed

### 1. **Observation Tree Well-Founded Order** ✅
**File**: `theories/Transform/CyclicTraceConditionObsTree.v`

Implemented and **fully proved** (no axioms):
- `obs_size : obs_tree -> nat` - size function for observation trees
- `lt_obs : obs_tree -> obs_tree -> Prop` - strict subtree order (via size)
- `lt_obs_wf : well_founded lt_obs` - **PROVED** using `lt_wf` on nat
- `lt_obs_of_in_recs` - key descent lemma: any recursive subtree is strictly smaller
- `lt_trace : option obs_tree -> option obs_tree -> Prop` - lifted to optional trees
- `lt_trace_wf : well_founded lt_trace` - **PROVED** via well-founded induction

**Status**: Complete, compiles, no axioms.

### 2. **Refactored Trace Condition** ✅ 
**File**: `theories/Transform/CyclicTraceCondition.v`

Changes:
- **Removed** `Axiom ltM_trace_wf`
- Changed `trace_state` from `option (nat * nat)` to `option SOR.obs_tree`
- Redefined `ltM_trace := CTO.lt_trace`
- **Proved** `ltM_trace_wf` using `CTO.lt_trace_wf` (no axiom!)
- Updated `ts_split` to represent "descend into recursive subtree" semantics
- Added helper `ltM_trace_of_ts_split` proving split steps strictly decrease

**Status**: Compiles, `ltM_trace_wf` is now a **Lemma** not an Axiom.

### 3. **Cycle-Progress Already Proven** ✅
**File**: `theories/Transform/SupercompileTraceCheckSound.v`

Already proved (from prior work):
- `trace_condition_ok_cycle_progress` - if the boolean trace check succeeds, every cycle contains a progress edge
- This discharges the `rc_cycle_progress` obligation in `Ranking.ranking_condition`

**Status**: Complete, no changes needed.

## What Remains

### 4. **Global Ranking Condition Witness** ⚠️
**File**: `theories/Transform/SupercompilationCorrespondence.v` (lines 1603-1608)

Current state:
```coq
Axiom supercompile_satisfies_trace_condition :
  forall Σenv fuel Γ t A v scb proof,
    SC.supercompile_jTy_tc fuel Σenv Γ t A = Some (v, scb) ->
    exists τ rank ltM, True.
```

**What's needed**:
1. Define a `rank : nat -> option obs_tree` function that extracts observation trees from vertex labels
2. Prove `rc_monotone`: rank doesn't increase along edges
3. Prove `rc_strict`: rank strictly decreases on progress edges (using `ltM_trace_of_ts_split`)
4. Connect to `supercompile_tc_cycle_progress` for `rc_cycle_progress`

**Why it's not trivial**:
- Need to relate `SC.cfg_builder` labels to observation trees
- Progress vertices (case-splits) must be shown to have corresponding observation-tree labels
- Requires connecting the supercompiler's term-level operations to semantic observation trees

**Possible approaches**:

**A) Defer to semantic correspondence** (pragmatic):
- Keep a lightweight axiom stating "if supercompilation terminates with trace check, then observation-tree ranking exists"
- Focus mechanization effort on the local correspondence (which is mostly done)

**B) Full mechanization** (rigorous but heavy):
- Extend `pp_label` in `ReadOffDrivingPreproof.v` to assign `jIndObs` labels to case-split vertices
- Prove that `SC.is_progress_vertex` aligns with `jIndObs` labels
- Show observation trees decrease across split edges via the semantics in `SequentObservationRules.v`

## Summary

**De-axiomatized**:
- ✅ Well-foundedness of observation-tree order (`lt_trace_wf`)
- ✅ Cycle-progress property (already proved via boolean check)

**Remaining axiom**:
- ⚠️ Global ranking witness connecting supercompiler graphs to observation trees

**Technical debt**: The remaining axiom is **not fundamental** - it's a matter of:
1. Engineering the label-assignment pass (assign `jIndObs` to progress vertices)
2. Proving local correspondence between splits and obs-tree descent
3. Composing with the already-proven cycle-progress

**Recommendation**: Accept the remaining axiom as "observation-tree extraction is correct" and focus on higher-level correspondence properties, OR budget ~1-2 days to fully mechanize the label assignment and prove the connection.

## Files Modified

1. `theories/Transform/CyclicTraceConditionObsTree.v` - NEW, 85 lines, **no axioms**
2. `theories/Transform/CyclicTraceCondition.v` - Updated, **removed axiom**, refactored to use obs_tree
3. `theories/dune` - Added `CyclicTraceConditionObsTree` to module list
4. `theories/Transform/SupercompilationCorrespondence.v` - No changes yet (axiom remains)

## Build Status

All modified files compile successfully:
```bash
dune build theories/Transform/CyclicTraceConditionObsTree.v  # ✅
dune build theories/Transform/CyclicTraceCondition.v          # ✅
```
