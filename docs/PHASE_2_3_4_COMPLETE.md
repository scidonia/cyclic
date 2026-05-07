# Phases 2, 3, and 4 Complete: Graph-Level Correspondence Theorems ✅

## Summary

All three core supercompilation correspondence theorems have been upgraded to **graph-level statements** that precisely relate the SC configuration graph to the cyclic proof graph.

## What Was Done

### Phase 2: Drive Correspondence ✅

**File:** `theories/Transform/SupercompilationCorrespondence.v:430-450`

**Theorem:** `drive_corresponds_to_async_edge`

**Statement:** When SC performs one-step call-by-name driving creating edge `v → w`, then:
- `w ∈ succ_of (builder_of t) v` (edge exists in proof graph)
- `pp_label fuel (builder_of t) w = jDrive (C.jTy Γ u A)` (successor labeled correctly)
- `SDR.drive_rule Σenv (C.jTy Γ t0 A) [C.jTy Γ u A]` (sequent rule valid)

**Proof technique:** Uses `bisim_succ_eq` and `bisim_label_exists` helper lemmas to extract graph properties from the bisimulation.

### Phase 3: Split Correspondence ✅

**File:** `theories/Transform/SupercompilationCorrespondence.v:478-501`

**Theorem:** `split_corresponds_to_sync_edge`

**Statement:** When SC splits on a neutral case-variable creating edges `v → w1, v → w2, ...`, then:
- For each successor `w ∈ ws`: `w ∈ succ_of (builder_of t) v` (all edges exist)
- For each successor: `pp_label fuel (builder_of t) w = jDrive cfg` (all labeled correctly)
- `SDR.drive_rule Σenv (C.jTy Γ (tCase ...) A) succs` (split rule valid)

**Proof technique:** Uses `bisim_succ_eq` to show edge correspondence, then quantifies over all successors to show each carries the correct branch configuration.

### Phase 4: Fold Correspondence ✅

**File:** `theories/Transform/SupercompilationCorrespondence.v:546-563`

**Theorem:** `memo_corresponds_to_fold`

**Statement:** When SC performs a memo hit creating backlink `v → v_prev`, then:
- `v_prev ∈ succ_of (builder_of t) v` (backlink exists in proof graph)
- Both vertices have matching labels: `pp_label v = jDrive cfg` and `pp_label v_prev = jDrive cfg`

**Proof technique:** Uses `bisim_succ_eq` and `bisim_label_exists` to show the backlink edge and label equality.

**Note:** This is the base correspondence; a complete treatment would also prove the cyclic validity condition (that `v_prev` is an ancestor of `v`).

## Verification

```bash
dune build  # ✅ Success
```

All three theorems compile and type-check correctly.

## Why This Matters

**Before:** The correspondence theorems were stated at the rule level only—they showed that SC operations satisfy sequent rules, but didn't connect the actual graph structures.

**After:** The correspondence theorems now state the precise relationship between:
1. SC configuration graph vertices and edges
2. Cyclic proof graph vertices and edges
3. How labels correspond
4. How rules are satisfied

This is the **core of the paper's claim:** "supercompilation IS cyclic proof search"—we now have formal graph-level correspondences for all three atomic operations.

## Statistics

- **Time:** ~45 minutes total
- **Lines modified:** ~50 lines in SupercompilationCorrespondence.v
- **New theorems proved:** 0 (upgraded existing theorems)
- **Build status:** ✅ All passing

## What's Next: Phase 5

**Remaining work:**
1. `supercompile_gives_valid_preproof`: Show that running the SC algorithm establishes the bisimulation
2. `supercompile_local_validity`: Extract local validity from the proven bisimulation

These are the "end-to-end" theorems that complete the correspondence by showing the bisimulation is actually maintained throughout supercompilation execution.

**Estimated time:** 5-7 days (per MECHANIZATION_PLAN.md)

## Files Modified

- `theories/Transform/SupercompilationCorrespondence.v`: Upgraded three correspondence theorems
- `MECHANIZATION_PLAN.md`: Updated success criteria and current status

## Key Insights

1. **Bisimulation helpers are essential:** The helper lemmas from Phase 1.2 make these proofs trivial—each proof is 3-5 lines.

2. **Graph-level vs rule-level:** The graph-level statements are strictly stronger—they imply the rule-level statements plus structural correspondence.

3. **Pattern is consistent:** All three theorems follow the same structure:
   - Take bisimulation + SC edge data
   - Use `bisim_succ_eq` to show edge correspondence
   - Use `bisim_label_exists` to show label correspondence
   - Apply the rule lemma to show validity

This pattern will guide Phase 5 proofs.
