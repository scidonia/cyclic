From Stdlib Require Import List Bool Arith Utf8.

From stdpp Require Import gmap.

From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile.
From Cyclic.Equiv Require Import CIUChecklistLengthMap.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.

(**
  A lightweight *inspection object* for supercompilation runs.

  The supercompiler builds a finite configuration graph (`cfg_builder`). For
  debugging/understanding, it is often helpful to view a *tree-shaped unfolding*
  from the root, with explicit back-links when a vertex is revisited.

  This file provides a small trace datatype plus a constructor that turns a
  `cfg_builder` into such a finite cyclic proof tree.
*)

Inductive trace_tree : Type :=
| TT_backlink (v : nat) (j : Supercompile.config)
| TT_node (v : nat) (j : Supercompile.config) (succs : list trace_tree).

Fixpoint mem_nat (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => Nat.eqb x y || mem_nat x ys
  end.

Fixpoint build_trace_tree
    (fuel : nat) (b : Supercompile.cfg_builder)
    (v : nat) (seen : list nat) : trace_tree :=
  match fuel with
  | 0 =>
      match Supercompile.lookup_label b v with
      | Some j => TT_backlink v j
      | None => TT_backlink v (C.jTy [] (tVar 0) (tVar 0))
      end
  | S fuel' =>
      match Supercompile.lookup_label b v with
      | None => TT_backlink v (C.jTy [] (tVar 0) (tVar 0))
      | Some j =>
          if mem_nat v seen then TT_backlink v j
          else
            match Supercompile.lookup_succ b v with
            | None => TT_node v j []
            | Some vs =>
                TT_node v j (map (fun w => build_trace_tree fuel' b w (v :: seen)) vs)
            end
      end
  end.

Definition trace_supercompile_jTy
    (fuel_sc fuel_tree : nat)
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option trace_tree :=
  match Supercompile.supercompile_jTy fuel_sc Σenv Γ t A with
  | None => None
  | Some (root, b) => Some (build_trace_tree fuel_tree b root [])
  end.

(**
  Convenience: an append-associativity index trace.

  This is not a theorem; it is meant to be inspected with:

    Eval vm_compute in trace_len_append_assoc_l.
*)

Definition Γ_lll : Ty.ctx := [ListNat.list_ty; ListNat.list_ty; ListNat.list_ty].

Definition t_len_append_assoc_l : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append
            (tApp (tApp ListNat.append (tVar 2)) (tVar 1)))
          (tVar 0)).

Definition trace_len_append_assoc_l : option trace_tree :=
  trace_supercompile_jTy 200 60 CIUChecklistLengthMap.Σ_listnat Γ_lll t_len_append_assoc_l Examples.nat_ty.
