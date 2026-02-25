# Core Theorem Mechanization Plan

## Current Status

### SupercompilationCorrespondence.v
- **drive_cbn_once_sound** (line 88-182): ✅ 95% complete (1 admit at line 164)
- **drive_corresponds_to_async_edge** (line 184-205): ❌ Stated, admitted
- **split_corresponds_to_sync_edge** (line 207-233): ❌ Stated, admitted  
- **memo_corresponds_to_fold** (line 235-256): ❌ Stated, admitted
- **supercompile_gives_valid_preproof** (line 258-281): ❌ Stated, admitted
- **supercompile_local_validity** (line 283-307): ❌ Stated, admitted

## Priority Order (Bottom-Up)

### Phase 1: Finish Foundation (1-2 days)

#### 1.1 Complete `drive_cbn_once_sound` ⭐ IMMEDIATE
**File:** `theories/Transform/SupercompilationCorrespondence.v:164`
**Blocker:** Need lemma `subst0_fix_not_identity`

```coq
Lemma subst0_fix_not_identity : forall A t,
  subst0 (tFix A t) t <> tFix A t.
```

**Strategy:**
- Show that `subst0 (tFix A t) t` increases de Bruijn index by 1 in at least one place
- Or show structural mismatch (substitution result has different shape)
- This should be provable by induction on `t` and properties of `subst0`

**Impact:** Unblocks the only partial proof, giving us 1 complete end-to-end lemma

#### 1.2 Understand bisimulation structure ⭐ CRITICAL
**Files:** 
- `theories/Transform/SupercompilationCorrespondence.v:52-78` (bisim definition)
- `theories/Transform/Supercompile.v` (cfg_builder structure)
- `theories/Transform/ReadOffDrivingPreproof.v` (rooted_preproof structure)

**Task:** Document the bisimulation components:
- What is `cb_label : V -> option config`?
- What is `cb_succ : V -> option (list V)`?
- How does `rooted_preproof` represent the same graph?
- What does "labels match up to extraction" mean precisely?

**Deliverable:** Write down the bisimulation invariants as comments/lemmas

### Phase 2: One Direction (3-4 days)

#### 2.1 Prove `drive_corresponds_to_async_edge` ⭐ HIGH PRIORITY
**Why this one first:** It's the simplest correspondence (deterministic, no branching)

**Proof strategy:**
1. Unfold bisimulation hypothesis to get vertex correspondence
2. Show `SC.drive_cbn_once t = u` with `u ≠ t`
3. Use `drive_cbn_once_sound` (now complete!) to get `SDR.drive_cbn_onceR t u`
4. Show this corresponds to an async edge in the proof graph
5. Show the successor vertex in SC graph matches the premise in proof graph

**Dependencies:**
- ✅ `drive_cbn_once_sound` (will be complete after 1.1)
- ❓ Need lemmas about `cb_succ` and proof graph `succ_of` correspondence
- ❓ Need `SDR.drive_rule` definition and its connection to `drive_cbn_onceR`

**Estimate:** 2 days once bisim structure is clear

#### 2.2 Add helper lemmas for bisimulation 
**Needed for 2.1:**

```coq
Lemma bisim_vertex_correspondence : 
  forall Σenv fuel scb proof v,
    bisim Σenv fuel scb proof ->
    v ∈ dom (cb_label scb) ->
    v ∈ verts (pp_graph (rpp_proof proof)).

Lemma bisim_label_match :
  forall Σenv fuel scb proof v cfg,
    bisim Σenv fuel scb proof ->
    cb_label scb !! v = Some cfg ->
    exists t A Γ,
      cfg = C.jTy Γ t A /\
      pp_label (rpp_proof proof) v = jDrive cfg.

Lemma bisim_succ_correspondence :
  forall Σenv fuel scb proof v ws,
    bisim Σenv fuel scb proof ->
    cb_succ scb !! v = Some ws ->
    succ_of (pp_graph (rpp_proof proof)) v = ws.
```

### Phase 3: Split Case (4-5 days)

#### 3.1 Prove `split_corresponds_to_sync_edge` ⭐ MEDIUM-HIGH PRIORITY
**Why this one:** Shows the correspondence handles branching

**Proof strategy:**
1. Given: SC splits on neutral `case x of {...}`
2. Show: `SC.split_case_var` produces multiple successors (one per constructor)
3. Show: Proof graph has corresponding `dr_split_case_var` rule
4. Show: Each SC successor matches a proof graph premise
5. Show: Contexts are extended correctly with constructor arguments

**Dependencies:**
- ✅ `drive_corresponds_to_async_edge` (provides pattern)
- ❓ Need `split_case_var` correctness lemma
- ❓ Need `SDR.dr_split_case_var` connection to `split_case_var_cfgs`

**Key insight:** `split_case_var` in SC and `split_case_var_cfgs` in sequent rules are literally the same function, so this should be straightforward once bisim is clear

**Estimate:** 3 days

### Phase 4: Folding (3-4 days)

#### 4.1 Prove `memo_corresponds_to_fold` ⭐ MEDIUM PRIORITY
**Why this one:** Shows cyclic closure correspondence

**Proof strategy:**
1. Given: SC finds `cfg` in memo table matching `cfg_prev`
2. Show: `judgement_eqb cfg cfg_prev = true`
3. Show: Proof graph has backlink `nBack` node
4. Show: Backlink target is the corresponding previous vertex
5. Use `judgement_eqb_eq` lemma (needs to be proved)

**Dependencies:**
- ❓ Need `judgement_eqb_eq : judgement_eqb j1 j2 = true -> j1 = j2`
- ❓ Need connection between memo lookup and `nBack` nodes in read-off
- ✅ Pattern established by drive/split correspondence

**Estimate:** 2-3 days

### Phase 5: End-to-End (1 week)

#### 5.1 Prove `supercompile_gives_valid_preproof` ⭐ HIGHEST IMPACT
**Why last:** Requires all previous lemmas

**Proof strategy:**
1. Induction on `supercompile_cfg` recursion structure
2. Base case: Initial configuration gives valid preproof root
3. Inductive step: Each SC operation preserves bisimulation
   - Drive → use `drive_corresponds_to_async_edge`
   - Split → use `split_corresponds_to_sync_edge`  
   - Fold → use `memo_corresponds_to_fold`
4. Show constructed graph satisfies all local rules
5. Show root vertex exists and is well-typed

**Dependencies:**
- ✅ All three correspondence lemmas (Phases 2-4)
- ❓ Need to unfold `supercompile_cfg` and analyze its recursion
- ❓ Need packaging lemmas from `ReadOffDrivingPreproof.v`

**Estimate:** 5 days once dependencies complete

#### 5.2 Prove `supercompile_local_validity` (Corollary)
**Easy once 5.1 is done:** Just extract local validity from bisimulation

## Total Estimates

- **Phase 1 (Foundation):** 2 days
- **Phase 2 (Drive):** 4 days
- **Phase 3 (Split):** 5 days
- **Phase 4 (Fold):** 4 days
- **Phase 5 (End-to-End):** 7 days

**Total:** ~22 working days (1 month)

## Parallelizable Work

While working on proofs, can also:
- **Documentation:** Add detailed comments to bisimulation definition
- **Examples:** Create concrete test cases (run SC on `length_map`, extract proof graph)
- **Paper:** Add proof sketches to appendix based on completed lemmas

## Risk Factors

### High Risk
- **Bisimulation definition may be wrong:** If the relation doesn't actually hold, proofs are impossible
  - **Mitigation:** Test on concrete examples first
  
- **Read-off packaging has bugs:** `ReadOffDrivingPreproof.v` has 5+ admits
  - **Mitigation:** May need to fix packaging before Phase 5

### Medium Risk
- **Split rule complexity:** Constructor arguments, context extensions, substitutions
  - **Mitigation:** Start with simple inductives (Nat, Bool) before List

- **SC implementation details:** Edge cases in `drive_cbn_once`, `split_case_var`
  - **Mitigation:** Add unit tests

## Success Criteria

### Minimal (Paper Credible)
- ✅ Phase 1 complete: `drive_cbn_once_sound` proved
- ✅ Phase 2 complete: `drive_corresponds_to_async_edge` proved (graph-level)
- ✅ One concrete example worked through (e.g., `length` function)

### Moderate (Strong Paper)
- ✅ Phases 1-3 complete: Drive + Split proved (both graph-level)
- ✅ Phase 4 complete: Fold/backlink correspondence proved (graph-level)
- ⏳ Three concrete examples worked through

### Full (Best Case)
- ⏳ Phase 5: End-to-end theorem proved
- ⏳ Multiple examples validated
- ⏳ Global soundness connected (trace condition)

## Current Status (Updated)

**Phases 1-4 COMPLETE** ✅

All three core correspondence theorems are now proved at the graph level:
1. **`drive_corresponds_to_async_edge`** (lines 430-450): Single-step driving = async edge
2. **`split_corresponds_to_sync_edge`** (lines 478-501): Case splitting = synchronous branching
3. **`memo_corresponds_to_fold`** (lines 546-563): Memo hit = backlink/fold

Each theorem now states:
- Graph structure correspondence (edges match)
- Label correspondence (vertex labels match)
- Rule validity (sequent rules are satisfied)

## Next Steps: Phase 5

**File:** `theories/Transform/SupercompilationCorrespondence.v:565+`

**Remaining theorems:**
- `supercompile_gives_valid_preproof`: End-to-end correctness
- `supercompile_local_validity`: Extract local validity from bisimulation

These require proving that the bisimulation is established and maintained throughout supercompilation.
