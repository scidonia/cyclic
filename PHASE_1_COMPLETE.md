# Phase 1.1 Complete: drive_cbn_once_sound ✅

## What Was Done

**File:** `theories/Transform/SupercompilationCorrespondence.v`
**Theorem:** `drive_cbn_once_sound` (lines 88-182)
**Status:** ✅ **FULLY PROVED** (no admits remaining)

## The Problem

The proof had 1 admit at line 164 in the `tFix` case:
```coq
+ (* scrut = tFix *)
  destruct (SC.tm_eqb (subst0 (tFix t1 t2) t2) (tFix t1 t2)) eqn:Heq.
  * exfalso. apply PU.tm_eqb_eq in Heq.
    admit. (* claimed this case was impossible *)
```

The comment claimed: "fix unfold always changes the term"

## The Solution

**Key insight:** Fixpoint unfolding CAN leave the term unchanged!

Example: `fix f. f` where body = `tVar 0`
- `drive_cbn_once (tFix A (tVar 0)) = subst0 (tFix A (tVar 0)) (tVar 0)`
- `(tVar 0).[tFix A (tVar 0)/0] = tFix A (tVar 0)`
- Result equals input → fixpoint is stuck

The `exfalso` was wrong. The correct proof uses `dc_case_scrut_stuck`:

```coq
+ (* scrut = tFix *)
  destruct (SC.tm_eqb (subst0 (tFix t1 t2) t2) (tFix t1 t2)) eqn:Heq.
  * (* stuck after unfold: happens when t2 = tVar 0 *)
    apply SDR.dc_case_scrut_stuck; [discriminate | constructor | ].
    apply PU.tm_eqb_eq in Heq. exact Heq.
  * (* changed after unfold *)
    apply SDR.dc_case_scrut_step; [discriminate | constructor | ].
    apply PU.tm_eqb_neq. auto.
```

## Verification

```bash
cd /home/gavin/dev/Scidonia/cyclic
dune build  # Compiles successfully
grep "admit\." theories/Transform/SupercompilationCorrespondence.v  # No output
```

## Impact

This completes the first concrete correspondence lemma! We now have:

**Theorem** (`drive_cbn_once_sound`): 
```coq
∀ t u, SC.drive_cbn_once t = u → SDR.drive_cbn_onceR t u
```

This shows that the *computational* driving function implements the *relational* driving specification correctly.

## What's Next

**Phase 1.2:** Document bisimulation structure (see MECHANIZATION_PLAN.md)

Then proceed to Phase 2: Prove `drive_corresponds_to_async_edge` (the first graph-level correspondence theorem)

## Statistics

- **Time:** ~10 minutes
- **Lines changed:** 7
- **Admits removed:** 1
- **Remaining admits in file:** 0
- **Remaining Admitted theorems:** 5 (the main correspondence theorems)
