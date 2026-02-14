# Bisimulation Structure Explained

## Overview

The correspondence between supercompilation and cyclic proof search is established through a **bisimulation** between two graph structures. This document explains how these structures relate.

## The Two Graphs

### 1. Supercompilation Graph (`SC.cfg_builder`)

**File:** `theories/Transform/Supercompile.v:629`

```coq
Record cfg_builder : Type := {
  cb_next : nat;                      (* Next fresh vertex ID *)
  cb_label : gmap nat config;          (* Vertex → Configuration *)
  cb_succ : gmap nat (list nat);       (* Vertex → Successors *)
  cb_inst : gmap nat (list tm);        (* Vertex → Instantiation args (for generalization) *)
  cb_holes : gmap nat (list tm);       (* Vertex → Hole types (for generalization) *)
}.
```

**Key points:**
- **Vertices:** Natural numbers (`nat`)
- **Labels:** `config` (which is `C.judgement`, typically `jTy Γ t A` for typing goals)
- **Edges:** `cb_succ !! v = Some ws` means vertex `v` has successors `ws`
- **Operations:**
  - Driving: adds async edges (deterministic unfolding)
  - Splitting: adds multiple successors (one per constructor)
  - Folding: adds backlink (single successor to previous vertex)

### 2. Cyclic Proof Graph (`rooted_preproof`)

**Files:** 
- `theories/Preproof/Preproof.v` (generic preproof structure)
- `theories/Transform/ReadOffDrivingPreproof.v` (packaging for SC)

```coq
Record rooted_preproof := {
  rpp_proof : preproof;   (* The actual proof graph *)
  rpp_root : V;           (* Root vertex *)
  rpp_root_in : ...;      (* Root is in graph *)
}.

Record preproof := {
  pp_graph : fin_digraph;       (* Finite directed graph *)
  pp_label : V -> Judgement;    (* Vertex labels *)
  pp_rule_ok : ...;             (* Local validity witness *)
}.
```

**The underlying builder (from ReadOff):**

```coq
Record builder : Type := {
  b_next : nat;
  b_label : gmap nat node;        (* Vertex → Node kind *)
  b_succ : gmap nat (list nat);   (* Vertex → Successors *)
  b_fix_ty : ...;                 (* Metadata for extraction *)
  b_fix_body : ...;
}.
```

**Key points:**
- **Vertices:** Same natural numbers as SC graph
- **Labels:** Sequent judgements (`jDrive`, `jObs`, `jSub`)
- **Edges:** `succ_of b v` gives successors of `v` in builder `b`
- **Rules:** Each vertex must satisfy a local sequent rule

## The Bisimulation Relation

**File:** `theories/Transform/SupercompilationCorrespondence.v:110`

```coq
Record bisim (Σenv : Ty.env) (fuel : nat)
    (scb : SC.cfg_builder) (proof : rooted_preproof Σenv (tVar 0)) : Prop := {
  bis_verts_eq : 
    dom scb.(SC.cb_label) = dom (RO.b_label (builder_of (tVar 0)));
  
  bis_label_match : forall v cfg,
    scb.(SC.cb_label) !! v = Some cfg ->
    exists t A Γ,
      cfg = C.jTy Γ t A /\
      pp_label fuel (builder_of (tVar 0)) v = jDrive cfg;
  
  bis_succ_match : forall v succs,
    scb.(SC.cb_succ) !! v = Some succs ->
    succ_of (builder_of (tVar 0)) v = succs;
  
  bis_local_valid : forall v,
    v ∈ dom scb.(SC.cb_label) ->
    rule Σenv (builder_of (tVar 0))
      (pp_label fuel (builder_of (tVar 0)) v)
      (map (pp_label fuel (builder_of (tVar 0))) 
           (succ_of (builder_of (tVar 0)) v));
}.
```

## What Each Invariant Means

### 1. `bis_verts_eq`: Same Vertices

```coq
dom scb.(SC.cb_label) = dom (RO.b_label (builder_of (tVar 0)))
```

**Meaning:** The set of vertices is identical in both graphs.

**Why it matters:** We can use vertex indices interchangeably. If SC has a vertex `v`, the proof graph has the same vertex `v`.

**Example:**
- SC graph: vertices {0, 1, 2, 5, 7}
- Proof graph: vertices {0, 1, 2, 5, 7}
- Both use same numbering scheme

### 2. `bis_label_match`: Labels Correspond

```coq
scb.(SC.cb_label) !! v = Some cfg ->
exists t A Γ, cfg = C.jTy Γ t A /\ pp_label fuel (builder_of (tVar 0)) v = jDrive cfg
```

**Meaning:** If SC vertex `v` is labeled with configuration `cfg = jTy Γ t A`, then the proof graph vertex `v` is labeled with `jDrive (jTy Γ t A)`.

**Why it matters:** The proof graph label contains the same sequent as the SC configuration. The `jDrive` wrapper indicates it's a driving/typing judgement (vs observation or substitution).

**Example:**
- SC: `cb_label !! 3 = Some (jTy [] (length l) Nat)`
- Proof: `pp_label 3 = jDrive (jTy [] (length l) Nat)`

### 3. `bis_succ_match`: Edges Correspond

```coq
scb.(SC.cb_succ) !! v = Some succs ->
succ_of (builder_of (tVar 0)) v = succs
```

**Meaning:** If SC vertex `v` has successors `[w1, w2, ...]`, then the proof graph vertex `v` has the same successors.

**Why it matters:** Graph structure is preserved. Operations that add/modify edges in SC are reflected in the proof graph.

**Example:**
- SC performs split on vertex 3: `cb_succ !! 3 = Some [4, 5]` (nil and cons branches)
- Proof graph: `succ_of b 3 = [4, 5]` (same branching structure)

### 4. `bis_local_valid`: Rules Are Satisfied

```coq
v ∈ dom scb.(SC.cb_label) ->
rule Σenv (builder_of (tVar 0)) (pp_label fuel v) (map (pp_label fuel) (succ_of v))
```

**Meaning:** Every vertex in the proof graph satisfies a local sequent rule. Given a vertex's label and its premises (successor labels), there exists a valid inference rule.

**Why it matters:** This ensures the proof graph is not just a random graph—it's a *locally valid* proof structure where each step is justified.

**Example:**
- Vertex 3: `jDrive (jTy [] (case l of {...}) Nat)`
- Successors 4, 5: `[jDrive (jTy [] zero Nat), jDrive (jTy [x:A, xs:List] (succ ...) Nat)]`
- Rule: `dr_split_case_var` (split on neutral variable `l`)

## Derived Helper Lemmas

We've added 8 helper lemmas to make working with bisimulation easier:

### Basic Helpers (Proven Trivially)

1. `vertex_in_sc_dom`: If SC has label for `v`, then `v ∈ dom cb_label`
2. `vertex_in_proof_graph`: If proof has label for `v`, then `v ∈ dom b_label`
3. `succ_lookup_some`: If SC has successors for `v`, then `v ∈ dom cb_succ`

### Bisimulation Extractors (Proven from `bisim`)

4. `bisim_vertex_in_proof`: `v ∈ dom scb → v ∈ dom proof` (by `bis_verts_eq`)
5. `bisim_vertex_in_sc`: `v ∈ dom proof → v ∈ dom scb` (by `bis_verts_eq`)
6. `bisim_label_exists`: Extract proof label from SC label (by `bis_label_match`)
7. `bisim_succ_eq`: Extract proof successors from SC successors (by `bis_succ_match`)
8. `bisim_vertex_valid`: Show specific vertex is locally valid (by `bis_local_valid`)

## How to Use in Correspondence Proofs

### Pattern for `drive_corresponds_to_async_edge`

```coq
Theorem drive_corresponds_to_async_edge :
  forall Σenv fuel scb proof v cfg cfg',
    bisim Σenv fuel scb proof ->          (* We have bisimulation *)
    scb.(SC.cb_label) !! v = Some cfg ->  (* SC has vertex v with cfg *)
    cfg' = drive_cfg cfg ->               (* SC drives to cfg' *)
    exists w,
      w ∈ succ_of (builder_of (tVar 0)) v /\  (* Proof has edge v → w *)
      pp_label fuel (builder_of (tVar 0)) w = jDrive cfg'.  (* w labeled with cfg' *)
Proof.
  intros ... Hbis Hlabel Hdrive.
  (* Use bisim_label_exists to get proof label *)
  pose proof (bisim_label_exists _ _ _ _ _ _ Hbis Hlabel) as Hproof_label.
  (* Use bisim_succ_eq to get proof successors *)
  ...
```

### Pattern for `split_corresponds_to_sync_edge`

```coq
Theorem split_corresponds_to_sync_edge :
  forall Σenv fuel scb proof v cfg splits,
    bisim Σenv fuel scb proof ->
    scb.(SC.cb_label) !! v = Some cfg ->
    splits = split_case_var cfg ->              (* SC splits *)
    scb.(SC.cb_succ) !! v = Some (map fst splits) ->
    Forall (fun '(w, branch_cfg) =>             (* Each branch matches *)
      pp_label fuel (builder_of (tVar 0)) w = jDrive branch_cfg
    ) splits.
Proof.
  intros ... Hbis Hlabel Hsplit Hsucc.
  (* Use bisim_succ_eq to connect SC successors to proof successors *)
  pose proof (bisim_succ_eq _ _ _ _ _ _ Hbis Hsucc) as Hproof_succ.
  (* Then show each successor is labeled correctly *)
  ...
```

## Next Steps for Phase 2

With bisimulation structure documented and helpers in place, we can now:

1. **Understand what needs to be proved:** The correspondence theorems connect:
   - SC operation (drive/split/fold) on `cfg_builder`
   - Proof graph structure (edges, labels) on `rooted_preproof`
   - Via bisimulation invariants

2. **Start proving `drive_corresponds_to_async_edge`:**
   - Given: `bisim scb proof` and `drive_cbn_once cfg = cfg'`
   - Show: Proof graph has edge `v → w` with `pp_label w = jDrive cfg'`
   - Use: `drive_cbn_once_sound` (already proved!) + bisim helpers

3. **Strategy:**
   - Extract components from bisimulation using helper lemmas
   - Connect `drive_cbn_once` to `drive_cbn_onceR` (via `drive_cbn_once_sound`)
   - Connect `drive_cbn_onceR` to `drive_rule` (sequent rule)
   - Show rule application = proof graph edge

## Key Insight

The bisimulation is the **bridge** between two worlds:
- **SC world:** Operational (functions that compute)
- **Proof world:** Declarative (relations that specify)

The correspondence theorems show: **SC operations = proof rule applications**
