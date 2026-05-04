# Paper-to-Repo Mapping

This file maps each claim, theorem, and proposition in the paper to its Rocq mechanisation.

## Claim 1: Pre-proof correspondence

| Paper | Rocq lemma | File |
|-------|-----------|------|
| Theorem 1 (Pre-proof) | `all_supercompiled_programs_yield_preproof` | `theories/Transform/SupercompilationCorrespondence.v` |
| Step: driving (async) | `drive_corresponds_to_async_edge` | same file |
| Step: splitting (sync) | `split_corresponds_to_sync_edge` | same file |
| Step: folding (backlink) | `memo_corresponds_to_fold` | same file |
| Proposition 3 (Vertex classification) | `cfg_vertex_drive_rule` | same file |

## Claim 2: Cyclic proof via budget trace

| Paper | Rocq lemma | File |
|-------|-----------|------|
| Theorem 2 (Cyclic proof) | `supercompile_yields_rooted_cyclic_proof` | `theories/Transform/SupercompilationCorrespondence.v` |
| Cycle-progress lemma | `trace_condition_ok_cycle_progress` | `theories/Transform/SupercompileTraceCheckSound.v` |
| Budget trace construction | `budget_trace_ranking_condition` | `theories/Transform/CyclicTraceConditionBudget.v` |

## Claim 3: CIU soundness

| Paper | Rocq lemma | File |
|-------|-----------|------|
| Theorem 3 (CIU untyped) | `supercompile_ciu_soundness_untyped` | `theories/Transform/SupercompilationCorrespondence.v` |
| Theorem 3 (CIU typed) | `supercompile_ciu_soundness_typed` | same file |
| CIU step lemma | `step_ciu`, `steps_ciu`, `ciu_tApp`, `ciu_apps`, `ciu_shift`, `ciu_subst0` | `theories/Equiv/CIU.v` |
| CIU case lemma | `ciu_case_branches_ciu` | `theories/Equiv/CIU.v` |
| CBN decomposition | `terminates_to_tApp_decompose`, `terminates_to_tCase_decompose` | `theories/Semantics/Cbn.v` |
| Driving CIU | `drive_cbn_once_ciu`, `whnf_drive_ciu` | `theories/Transform/SupercompilationCorrespondence.v` |
| Generalisation CIU | `ciu_generalise` | same file |
| Self-loop protection | `trace_condition_ok_no_self_loop` | `theories/Transform/SupercompileTraceCheckSound.v` |
| Typing shift | `has_type_shift` | `theories/Judgement/Typing.v` |
| Typing subst | `has_type_subst` | `theories/Judgement/Typing.v` |
| Typing weaken | `has_type_weaken_head` | `theories/Judgement/Typing.v` |
| Residualiser typing | `residualise_cfg_root_typing` | `theories/Transform/SupercompilationCorrespondence.v` |

## Claim 4: Example validation

| Paper | Rocq artefact | File |
|-------|-------------|------|
| Length-map fusion | `CIUChecklistLengthMap.v` | `theories/Equiv/` |
| Full example suite | `SupercompileChecklistIndexPipeline.v` | `theories/Equiv/` |
| Supercompiler test | `SupercompileTest.v` | `theories/Transform/` |

## Sequent calculus

| Paper | Rocq artefact | File |
|-------|-------------|------|
| Driving rules | `SequentDrivingRules.v` | `theories/Transform/` |
| Observation rules | `SequentObservationRules.v` | `theories/Transform/` |
| Vertex spec | `CyclicVertexSpec.v` | `theories/Transform/` |

## Build

```
dune build
```

Requires Rocq 9.1.0, stdpp, and Autosubst.
