# Read-Off/Extract Correctness Proof Status

## Goal
Prove `extract_read_off_id : extract_read_off t = t`, which shows that the extraction phase correctly inverts the read-off compilation phase. This is the main round-trip theorem for the cyclic proof pipeline.

## Current Status

### ✅ Completed
- File structure and module imports
- Basic helper lemmas (fix_env_of, targets tracking, apps_tm, app_view)
- Builder well-formedness definitions (dom_lt, closed_lt, preserves_lt)
- Fresh/put/put_fix_ty preservation lemmas  
- All infrastructure compiles without errors

### ⚠️ Admitted (Provable)
These lemmas are admitted due to tactical complexity, but the snapshot file proves they're all provable:

1. **compile_tm_preserves_lt** (line 433)
   - Shows compilation preserves vertices < old b_next
   - Issue: Complex tactic interactions with destruct/simpl/try
   - Solution: See snapshot line 390-455 for working proof

2. **compile_tm_list_bnext_mono_mutual** (line 454)
   - Mutual induction showing b_next monotonicity  
   - Issue: Complex case analysis on all term constructors
   - Solution: See snapshot line 442-566 for working proof

3. **compile_tm_dom_lt / compile_list_dom_lt** (line 580)
   - Domain bound preservation
   - Issue: Mutual recursion with many cases
   - Solution: See snapshot line 686-846 for working proof

4. **compile_tm_root_lt** (line 587)
   - Root vertex bounds
   - Solution: See snapshot for proof structure

5. **compile_list_roots_lt** (line 634)
   - List vertex bounds
   - Solution: See snapshot for proof structure

6. **build_subst_chain_closed_lt** (line 660)
   - Closedness for substitution chains
   - Solution: See snapshot for proof structure

7. **subst_args_build_subst_chain** (line 668)
   - Substitution extraction correctness
   - Solution: See snapshot line 1650+ for proof

8. **Helper lemmas** (targets_lt_mono, nodup_targets_cons_fresh, etc.)
   - Simple proofs, admitted to save time
   - All have straightforward proofs in snapshot

9. **compile_tm_closed / compile_list_closed**
   - Closedness preservation during compilation
   - Complex mutual induction, see snapshot line 862+

### 🔴 Major Work Remaining

#### 1. Extract_ext Section (HIGH PRIORITY)
**Location in snapshot:** Lines 1439-1605  
**Purpose:** Proves extraction is stable under builder extension  
**Key Lemma:** `extract_ext`
```coq
Lemma extract_ext (fuel : nat) :
  (forall v, v < n -> EX.extract_v fuel b ρ v = EX.extract_v fuel b' ρ v)
  /\ (forall v, v < n -> EX.extract_node fuel b ρ v = EX.extract_node fuel b' ρ v)
  /\ (forall sv, sv < n -> EX.subst_args fuel b ρ sv = EX.subst_args fuel b' ρ sv).
```

**What it does:**
- Shows that if builders b and b' agree on vertices < n
- And those vertices are closed (successors also < n)
- Then extraction from b and b' produces the same terms

**Why it's needed:**
- During compilation, we build intermediate builders b1, b2, b3...
- We need to lift extraction correctness from b1 to b2, b3, etc.
- This lemma provides that lifting

**Proof structure:**
- Induction on fuel
- Case analysis on each node constructor (nPi, nLam, nApp, nRoll, nCase, nBack, etc.)
- For each case, use closedness to show successors are also < n
- Apply IH to prove equality

**Status:** Complete proof exists in snapshot, needs careful porting

#### 2. Extract_compile_tm (HIGHEST PRIORITY)
**Location in snapshot:** Lines 1685-2265  
**Purpose:** Main correctness theorem - extraction inverts compilation  
**Key Theorem:**
```coq
Lemma extract_compile_tm (fuel : nat) (ρ : RO.back_env) (t : T.tm) (b : RO.builder) :
  fuel >= T.size t ->
  dom_lt b ->
  closed_lt b (RO.b_next b) ->
  nodup_targets ρ ->
  targets_lt ρ (RO.b_next b) ->
  let '(v, b') := RO.compile_tm fuel ρ t b in
  EX.extract_v fuel b' (fix_env_of ρ) v = t.
```

**What it does:**
- For any term t compiled with environment ρ to vertex v in builder b'
- Extracting v from b' with fix_env_of ρ gives back t

**Why it's needed:**
- This is the heart of the round-trip proof
- extract_read_off_id follows immediately from this

**Proof structure:**
- Mutual induction on fuel and term structure
- For each term constructor:
  * Compile subterms to intermediate builders
  * Use extract_ext to lift extraction across builder changes
  * Apply IH to show subterms extract correctly  
  * Combine to show whole term extracts correctly
- Complex cases: tFix (cycle creation), tApp backlinks

**Status:** Complete proof exists in snapshot, needs careful porting  
**Difficulty:** ~580 lines, many interdependent lemmas

#### 3. Extract_read_off_id (FINAL STEP)
**Location:** Line 731  
**Purpose:** The main theorem we want  
**Status:** Should be straightforward once extract_compile_tm is ported

**Proof sketch:**
```coq
Theorem extract_read_off_id (t : T.tm) : EX.extract_read_off t = t.
Proof.
  unfold EX.extract_read_off.
  destruct (RO.read_off_raw t) as [root b] eqn:H.
  unfold RO.read_off_raw in H.
  (* read_off_raw = compile_tm (T.size t) [] t empty_builder *)
  apply (extract_compile_tm (T.size t) [] t RO.empty_builder).
  - lia. (* fuel >= size *)
  - apply dom_lt_empty.
  - apply empty builder is closed
  - nodup_targets []
  - targets_lt [] (b_next empty)
Qed.
```

## Roadmap

### Phase 1: Port extract_ext (Est. 2-4 hours)
1. Copy section structure from snapshot
2. Port helper lemmas (lookup_node_agree, lookup_succ_agree, fix_ty_agree)
3. Port main extract_ext proof
   - Handle each node constructor case carefully
   - Ensure Forall reasoning works correctly
   - Use map congruence lemmas where needed

### Phase 2: Port extract_compile_tm (Est. 4-8 hours)
1. Port fuel adequacy and size lemmas (size_le_fold_right, etc.)
2. Set up mutual induction structure
3. Port each term constructor case:
   - tVar, tSort: simple
   - tPi, tLam: handle binder environment extension
   - tApp: handle backlink vs ordinary app
   - tFix: handle cycle creation and target tracking
   - tInd, tRoll, tCase: handle lists of subterms
4. Port helper lemma for compile_list extraction
5. Debug and fix any porting issues

### Phase 3: Complete extract_read_off_id (Est. 1 hour)
1. Apply extract_compile_tm with empty builder/environment
2. Verify all preconditions
3. Close the proof

### Phase 4: Polish (Est. 1-2 hours)
1. Go back and complete admitted tactical lemmas if time permits
2. Add documentation comments
3. Clean up proof structure

## Key Insights

### Why this proof is hard
1. **Mutual recursion:** compile_tm/compile_list and extract_v/extract_node/subst_args are mutually recursive
2. **Builder threading:** Need to track how builders evolve through compilation
3. **Environment correspondence:** Back-env (RO.back_env) must correspond to fix-env (EX.fix_env)
4. **Cycle handling:** tFix creates cycles by tying knots, extraction must untie them correctly
5. **Fresh vertex allocation:** Compilation allocates fresh vertices, must prove they stay in bounds

### Why snapshot proves it's doable
- Complete working proof exists
- All lemmas are proven
- Structure is sound
- Just needs careful porting with attention to:
  * Variable names from destructuring
  * Tactic interaction (destruct/simpl/try)
  * Bullet point alignment
  * Hypothesis management in large proofs

## References
- Main file: `theories/Transform/ReadOffExtractCorrectness.v`
- Reference: `theories/Transform/ReadOffExtractCorrectness_Snapshot.v`
- ReadOff: `theories/Transform/ReadOff.v` (defines compilation)
- Extract: `theories/Transform/Extract.v` (defines extraction)

## Notes
- The snapshot was created during an interrupted proof session
- All infrastructure is sound, just needs final assembly
- Tactical issues are NOT fundamental - snapshot proves proofs exist
- Main challenge is careful porting of large case analyses
