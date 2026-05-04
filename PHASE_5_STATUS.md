# Phase 5 Status: End-to-End Correspondence

## Overview

Phase 5 aims to prove that supercompilation execution produces a valid cyclic proof. This requires connecting three components:
1. **Supercompilation** (`Supercompile.v`): produces `cfg_builder`
2. **Residualization** (`Supercompile.v`): converts `cfg_builder` → residual term
3. **Read-off** (`ReadOff.v` + `ReadOffDrivingPreproof.v`): converts term → `rooted_preproof`

## Current Status

### ✅ What's Done

1. **Core correspondence theorems (Phases 2-4):** All three atomic operations (drive, split, fold) have graph-level correspondence proofs.

2. **Bisimulation relation:** Well-defined relation between `cfg_builder` and `rooted_preproof` with helper lemmas.

3. **Local validity corollary:** `supercompile_local_validity` proved (lines 619-628) - shows that if bisimulation holds, local validity follows.

4. **Architecture clarification:** Identified that the end-to-end proof requires showing:
   ```
   supercompile_jTy → (v, scb)
       ↓ residualize
   t_res
       ↓ read_off
   rooted_preproof
       ↓ check
   bisim scb t_res proof
   ```

### ⏳ What Remains

#### 1. Main Theorem: `supercompile_gives_valid_preproof`

**Current statement** (lines 565-591):
```coq
Theorem supercompile_gives_valid_preproof :
  forall Σenv fuel Γ t_input A v scb t_res,
    SC.supercompile_jTy fuel Σenv Γ t_input A = Some (v, scb) ->
    exists (proof : rooted_preproof Σenv t_res),
      bisim Σenv fuel scb t_res proof.
```

**Status:** Admitted

**Why it's hard:**
- Requires proving that `cfg_builder` structure matches read-off graph structure
- Need to show residualization preserves graph properties
- Must handle all three SC operations (drive, split, fold) in the induction
- Generalization complicates the proof (introduces new vertices)

**What's needed:**
1. **Structural invariants** (Axiom, line 596): `cfg_builder_well_formed`
   - All successors are valid vertices
   - Root vertex exists
   - Labels are well-typed configurations

2. **Read-off properties** (Axiom, line 604): `readoff_preserves_structure`
   - Read-off produces well-formed builders
   - Successors are valid
   
3. **Residualization correctness:**
   - Residualized term structure matches cfg_builder structure
   - Read-off of residual term gives back the same graph shape

4. **Induction principle:**
   - Need to induct on `supercompile_cfg` execution
   - Show each step preserves bisimulation invariants
   - Use correspondence theorems from Phases 2-4

#### 2. Helper Lemmas

The following lemmas would make the proof tractable:

**a) Initial bisimulation:**
```coq
Lemma bisim_initial :
  forall Σenv Γ t A,
    (* Fresh cfg_builder with single node labeled (jTy Γ t A) *)
    (* is bisimilar to read_off t *)
    ...
```

**b) Bisimulation preservation:**
```coq
Lemma bisim_preserved_drive :
  forall Σenv fuel scb scb' t proof v w,
    bisim Σenv fuel scb t proof ->
    (* scb' is scb with v→w edge added via drive *)
    SC.cb_succ scb' !! v = Some [w] ->
    ...
    bisim Σenv fuel scb' t proof'.

Lemma bisim_preserved_split :
  forall Σenv fuel scb scb' t proof v ws,
    bisim Σenv fuel scb t proof ->
    (* scb' is scb with v→ws edges added via split *)
    ...
    bisim Σenv fuel scb' t proof'.

Lemma bisim_preserved_fold :
  forall Σenv fuel scb scb' t proof v v_prev,
    bisim Σenv fuel scb t proof ->
    (* scb' is scb with v→v_prev backlink added *)
    ...
    bisim Σenv fuel scb' t proof'.
```

**c) Residualization/read-off round-trip:**
```coq
Lemma residualize_readoff_isomorphic :
  forall fuel Σenv v scb,
    let t_res := SC.residualise_cfg fuel Σenv scb v 0 ∅ in
    let b_res := snd (RO.read_off_raw t_res) in
    (* Graph structures are isomorphic *)
    dom (SC.cb_label scb) = dom (RO.b_label b_res) /\
    (forall w, SC.cb_succ scb !! w = RO.b_succ b_res !! w).
```

## Estimated Effort

**Original estimate:** 5-7 days

**Revised estimate:** 10-15 days for full proof

**Breakdown:**
- Structural invariant proofs: 2-3 days
- Residualization round-trip: 3-4 days  
- Bisimulation preservation lemmas: 3-4 days
- Main induction: 2-3 days

**Alternative: Partial results**

If the full proof is too costly, we can:
1. ✅ Keep the axioms and corollary (already done)
2. ✅ Document what's needed clearly (this file)
3. State in the paper: "Core correspondence theorems proved, end-to-end composition axiomatized"

This is academically honest and still represents significant progress.

## What's Valuable Right Now

The **real value** of Phases 2-4 is:
- ✅ **Precise graph-level correspondences** for all three SC operations
- ✅ **Bisimulation infrastructure** with helper lemmas
- ✅ **Local validity** follows from bisimulation (proved)

These are the **core contributions**. The end-to-end composition is "plumbing" that connects components but doesn't add new insights.

## Recommendation

**For the paper:**
1. Present the three proved correspondence theorems (Phases 2-4)
2. Present the bisimulation framework
3. State the end-to-end theorem and explain the architecture
4. Note that the main theorem is "axiomatized pending residualization/read-off analysis"

**For future work:**
1. Prove `cfg_builder_well_formed` by induction on `supercompile_cfg`
2. Prove `residualize_readoff_isomorphic` by analyzing both functions
3. Use these to complete the main theorem

## Files Modified

- `theories/Transform/SupercompilationCorrespondence.v`: Reformulated end-to-end theorems, added helper axioms, proved `supercompile_local_validity` corollary
- `PHASE_5_STATUS.md`: This file (architectural documentation)

## Summary

**Phases 2-4: COMPLETE** ✅  
**Phase 5: PARTIAL** ⏳
- Architecture understood ✅
- Helper lemmas identified ✅  
- Local validity proved ✅
- Main theorem stated and axiomatized ⏳
- Full proof remains future work ⏳

This represents **substantial progress** on the mechanization and provides a clear roadmap for completion.
