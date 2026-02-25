From Stdlib Require Import List Bool Arith Lia Utf8.
From stdpp Require Import prelude gmap fin_sets.

From Cyclic.Graph Require Import FiniteDigraph.
From Cyclic.Transform Require Import Supercompile.

Import ListNotations.

Set Default Proof Using "Type".

Module SC := Supercompile.

(** Attempt to de-axiomatize the SCC-based nonprogress cycle checker.

    Goal (completeness direction):
      if the nonprogress cfg graph has a directed cycle, then
      [SC.has_nonprogress_cycle] returns [true].

    This is the core missing step needed to prove that
      [SC.trace_condition_ok b = true]
    implies "no nonprogress cycles".

    We intentionally work over the numeric universe [0 .. n-1]
    where [n = cb_next b], matching the SCC implementation.
*)

Section SCC.

  Definition in_range (n v : nat) : Prop := v < n.

  Definition verts_range (n : nat) : gset nat := list_to_set (seq 0 n).

  Lemma elem_of_verts_range (n v : nat) :
    v ∈ verts_range n <-> v < n.
  Proof.
    unfold verts_range.
    rewrite elem_of_list_to_set.
    rewrite elem_of_seq.
    lia.
  Qed.

  (** The raw cfg graph over [0..n-1]. *)
  Definition cfg_graph_range (b : SC.cfg_builder) (n : nat)
      (Hrange : forall v w, v < n -> w ∈ SC.succs_of b v -> w < n)
      : @FiniteDigraph.fin_digraph nat _ _ :=
    {| FiniteDigraph.verts := verts_range n;
       FiniteDigraph.succ := SC.succs_of b;
       FiniteDigraph.succ_closed :=
         (fun v Hv =>
            (* turn range closure into set membership closure *)
            let Hv' : v < n := (proj1 (elem_of_verts_range n v) Hv) in
            (proj2 (Forall_forall (fun w => w ∈ verts_range n) (SC.succs_of b v))
              (fun w Hw => (proj2 (elem_of_verts_range n w)) (Hrange v w Hv' Hw))))
    |}.

  (** A cycle in the numeric-range graph implies the SCC detector flags it.

      This is the main completeness theorem we ultimately want.
      The proof requires correctness of [kosaraju_scc] with respect to
      [FiniteDigraph.is_cycle].

      This file contains the initial proof infrastructure; the final proof
      remains future work.
  *)
  Theorem cycle_implies_has_nonprogress_cycle :
    forall (b : SC.cfg_builder) n Hrange xs,
      n = SC.cb_next b ->
      FiniteDigraph.is_cycle (cfg_graph_range b n Hrange) xs ->
      SC.has_nonprogress_cycle b = true.
  Proof.
    intros b n Hrange xs -> Hcyc.
    (* TODO: Prove completeness of kosaraju_scc.

       High-level proof sketch:
       1. Show every directed cycle lies within some SCC.
       2. Show kosaraju_scc returns SCCs (sound+complete).
       3. Therefore some component has size>=2, or a self-loop.
       4. Therefore the existsb check in has_nonprogress_cycle is true.

       The key missing ingredient is a verified connection between:
         kosaraju_scc (2*(n+1)) n b
       and strongly connected components of the graph.
    *)
  Admitted.

End SCC.
