# Kanban

## Done

- [x] `has_type_subst` and `has_type_weaken_head` proved (WF induction on `T.size t`)
- [x] `has_type_subst_ren` (renaming-only) proved, breaks the circular dependency
- [x] `backlink_admissible` Qed (4-line corollary of CIU theorem)
- [x] Full build at 0 errors, 0 additional Admitted beyond pre-existing files
- [x] Admissibility paper drafted (7 pages, LLNCS)

## In progress

- [ ] ESOP 2027 paper — compact notation, typing rules, submission polish
- [ ] HLS 2027 paper — supercompiler as cyclic proof search for CIC

## Backlog

### Substitution supercompilation
- [ ] **Supercompile the substitution terms in backlink/generalisation.**
      Currently `cb_inst` stores bare `list tm` from anti-unification.
      The `jSub` rule gives each `σ[i]` a typing `jTy Δ σ_i (σ_{<i}(Γ[i]↑))`
      — a fully valid configuration for `supercompile_cfg`.  The fix:
      store `jSub` as a structured node with `jTy` premises, enumerate those
      as successors during supercompilation, inline their residuals as the
      `apps` arguments at readback.  This closes the one gap where
      substitution terms escape the supercompiler's reach.

### ty_roll design limitation
- [ ] `ty_roll` uses `ctor_param_tys` directly without applying the ambient
      substitution.  This forces the `closed_param_tys` side condition on
      `has_type_subst` / `has_type_weaken_head`.  For parametric inductives
      (`Vec`, `List`) whose constructor param types contain free `tVar`
      entries, the condition fails and the substitution lemmas don't hold.
      The correct fix: parameterise `ty_roll` to carry the instantiated
      parameter types, or store `ctor_param_tys` as a telescope relative to
      `ind_params` and substitute on constructor application.

### Coinductive generalisation
- [ ] Extend the soundness argument to proof systems where the cyclic
      structure is not given as a finite graph in advance (lazy generation,
      infinite but regular trees).  This requires reformulating the
      progress condition as a coinductive invariant and the soundness
      argument as a productivity/guardedness proof in CIC.  Mentioned in
      the admissibility paper as future work.

### Paper polishing
- [ ] ESOP 2027: LLNCS formatting compliance, page budget, bibliography
- [ ] HLS 2027: integrate cyclic proof / supercompiler correspondence
- [ ] Admissibility: add Brotherston comparison, submission-ready polish
