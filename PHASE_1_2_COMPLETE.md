# Phase 1.2 Complete: Bisimulation Structure Documented ✅

## What Was Done

**Files Modified:**
- `theories/Transform/SupercompilationCorrespondence.v` (lines 43-133)
- `BISIMULATION_EXPLAINED.md` (new comprehensive documentation)

**Status:** ✅ **COMPLETE** - Bisimulation fully documented with helper lemmas

## Changes Made

### 1. Documentation Block (60 lines)

Added comprehensive overview explaining:
- Two graph structures (SC cfg_builder vs proof rooted_preproof)
- What each side contains (vertices, labels, edges, metadata)
- The correspondence invariants
- How they connect operationally

### 2. Helper Lemmas (8 lemmas, all proved)

#### Basic Helpers
```coq
Lemma vertex_in_sc_dom : cb_label !! v = Some cfg -> v ∈ dom cb_label
Lemma vertex_in_proof_graph : b_label !! v = Some lbl -> v ∈ dom b_label  
Lemma succ_lookup_some : cb_succ !! v = Some succs -> v ∈ dom cb_succ
```

#### Bisimulation Extractors
```coq
Lemma bisim_vertex_in_proof : bisim + v ∈ dom scb → v ∈ dom proof
Lemma bisim_vertex_in_sc : bisim + v ∈ dom proof → v ∈ dom scb
Lemma bisim_label_exists : bisim + SC label → proof label
Lemma bisim_succ_eq : bisim + SC successors → proof successors
Lemma bisim_vertex_valid : bisim + SC label → vertex satisfies rule
```

### 3. Local Notation

```coq
Local Notation "'builder_of' t" := (snd (RO.read_off_raw t))
Local Notation "'root_of' t" := (fst (RO.read_off_raw t))
```

Reduces repetitive `(snd (RO.read_off_raw (tVar 0)))` in proofs.

### 4. Comprehensive External Documentation

**File:** `BISIMULATION_EXPLAINED.md` (320 lines)

Contents:
- Overview of both graph structures
- Detailed explanation of each invariant
- What each helper lemma does
- Usage patterns for correspondence proofs
- Examples of how to apply in Phase 2
- Key insights about the SC/proof world bridge

## Verification

```bash
cd /home/gavin/dev/Scidonia/cyclic
dune build  # Compiles successfully ✅
```

All 8 helper lemmas are proved (no admits).

## Why This Matters

**Before Phase 1.2:**
- Bisimulation was a black box
- Unclear how to extract properties
- Each proof would need to manually destruct bisim record

**After Phase 1.2:**
- Clear mental model of correspondence
- Helper lemmas provide clean interface
- Proofs can use `bisim_label_exists` instead of pattern matching
- Documentation serves as reference during Phase 2

## Example: How Phase 2 Will Use This

### Without helpers (old approach):
```coq
Proof.
  intros Σenv fuel scb proof v cfg Hbis Hlabel.
  destruct Hbis as [Hverts Hlabelmatch Hsuccmatch Hvalid].
  destruct (Hlabelmatch v cfg Hlabel) as [t [A [Γ [Hcfg Hpplabel]]]].
  subst cfg.
  (* Now we can use Hpplabel... *)
```

### With helpers (new approach):
```coq
Proof.
  intros Σenv fuel scb proof v cfg Hbis Hlabel.
  pose proof (bisim_label_exists _ _ _ _ _ _ Hbis Hlabel) as Hpplabel.
  (* Directly get proof label, 1 line instead of 4 *)
```

## Statistics

- **Time:** ~30 minutes
- **Lines added:** ~130 (Coq) + 320 (documentation)
- **Lemmas added:** 8 (all proved)
- **Documentation created:** 1 comprehensive guide

## What's Next

**Phase 2: Prove `drive_corresponds_to_async_edge`**

With bisimulation structure understood and helpers in place, we can now:

1. State the theorem precisely (graph-level correspondence)
2. Use `drive_cbn_once_sound` (Phase 1.1 result)
3. Apply bisimulation helpers to extract properties
4. Connect SC drive operation to proof graph async edge
5. Show vertices and labels match via bisim invariants

**Estimated time:** 4 days (per MECHANIZATION_PLAN.md)

The foundation is solid. We're ready to prove actual correspondence theorems!
