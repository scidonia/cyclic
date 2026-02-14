From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap fin_sets.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Preproof Require Import Preproof.
From Cyclic.Transform Require Import ReadOff ReadOffDrivingPreproof SequentDrivingRules SequentObservationRules Extract.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module RO := ReadOff.
Module RDP := ReadOffDrivingPreproof.
Module SDR := SequentDrivingRules.
Module SOR := SequentObservationRules.
Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module Extr := Extract.

(** Graph rewrite system for supercompilation (Task 2)

    This file defines `sc_step_async : ProofGraph -> ProofGraph -> Prop`,
    the relation that rewrites cyclic proof graphs by applying one
    driving or observation move.

    The rewrite system operates on `rooted_preproof` objects produced by
    `ReadOffDrivingPreproof.rooted_preproof_of`.

    Asynchronous moves (deterministic/invertible):
    - Apply one `drive_rule` step (β-reduction, fix-unfolding, iota, etc.)
    - Apply one observation-driving step (descend under constructors)
    - Apply case-case commuting conversions

    These moves replace a vertex with a new vertex (or vertices) and update
    the graph structure accordingly.
*)

Section Rewrite.
  Import RDP.Packaging.

  (** A proof graph is a rooted preproof with our combined judgement type *)
  Definition ProofGraph := 
    @rooted_preproof judgement (fun j ps => rule ∅ (RO.empty_builder) j ps) V _ _.

  (** Apply a driving rule to a single vertex.
  
      Given a vertex v labeled with jDrive (jTy Γ t A), if drive_rule
      justifies a step from t to u, replace v with a new vertex v' labeled
      with jTy Γ u A.
      
      For now, this is a high-level specification. The actual implementation
      would need to:
      1. Identify the vertex v in the graph
      2. Check if drive_rule applies to the term at v
      3. Create a new vertex v' with the driven term
      4. Update all edges pointing to v to point to v'
      5. Prove the result is still a valid preproof
  *)
  Inductive sc_step_drive (Σenv : Ty.env) : ProofGraph -> ProofGraph -> Prop :=
  | ssd_placeholder : forall pg1 pg2,
      (* TODO: Implement drive step *)
      (* For now, never applies *)
      False ->
      sc_step_drive Σenv pg1 pg2.

  (** Apply an observation-driving rule to a single vertex.
  
      Similar to sc_step_drive, but for observation judgements.
      This handles the case where we've identified a Nat-typed subgoal
      and want to drive under Succ constructors.
  *)
  Inductive sc_step_observe (Σenv : Ty.env) : ProofGraph -> ProofGraph -> Prop :=
  | sso_placeholder : forall pg1 pg2,
      (* TODO: Implement observation step *)
      False ->
      sc_step_observe Σenv pg1 pg2.

  (** Asynchronous supercompilation step: apply one driving or observation move *)
  Inductive sc_step_async (Σenv : Ty.env) : ProofGraph -> ProofGraph -> Prop :=
  | ssa_drive pg1 pg2 :
      sc_step_drive Σenv pg1 pg2 ->
      sc_step_async Σenv pg1 pg2
  | ssa_observe pg1 pg2 :
      sc_step_observe Σenv pg1 pg2 ->
      sc_step_async Σenv pg1 pg2.

End Rewrite.

(** Design notes for implementation:

    The actual implementation of sc_step_drive and sc_step_observe will need:
    
    1. **Vertex selection**: A way to pick which vertex to rewrite
       - Could be explicit (take vertex ID as parameter)
       - Could be non-deterministic (existentially quantified)
    
    2. **Graph surgery**: Operations to modify the graph
       - Add new vertices
       - Update edge targets
       - Preserve graph validity (all edges point to valid vertices)
    
    3. **Rule application**: Check that SequentDrivingRules.drive_rule applies
       - Extract terms from vertices using Extr.extract_v
       - Apply rule to get successor configuration(s)
       - Create new vertices for successors
    
    4. **Preservation proof**: Show the result is a valid rooted_preproof
       - pp_rule_ok must hold for all vertices
       - Root must remain in the vertex set
       - Graph must remain finite
    
    This is substantial work and may require refactoring the Preproof interface
    to support mutation operations. For the MVP, we can:
    - Define the high-level interface (done above)
    - Implement a single concrete example (e.g., β-reduction on a specific term)
    - Prove preservation for that example
    - Generalize once we understand the patterns
*)
