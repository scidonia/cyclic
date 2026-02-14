From Stdlib Require Import List Utf8.

From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile.
From Cyclic.Equiv Require Import CIUChecklistLengthMap.

Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.

(**
  Additional checklist-style examples showing that supercompilation can be used
  to normalize *indices* in dependent types.

  All proofs are by computation (`vm_compute`), and therefore do not rely on any
  of the still-admitted semantic theorems.
*)

(** A plausible environment where Nat=0, List=1, Vec=2. *)
Definition Σ_listnat_vec : Ty.env := [Examples.Nat_sig; ListNat.List_sig; Examples.Vec_sig].

Definition vec_ty_sc (n : tm) : tm := tInd 2 [Examples.nat_ty; n].

Lemma residual_vec_index_exact :
  option_map vec_ty_sc residual_len_map = option_map vec_ty_sc residual_len.
Proof.
  unfold residual_len_map, residual_len.
  vm_compute.
  reflexivity.
Qed.

(** Classic: length (append l1 l2) = plus (length l1) (length l2). *)

Definition Γ_ll : Ty.ctx := [ListNat.list_ty; ListNat.list_ty].

Definition t_len_append : tm :=
  tApp ListNat.length (tApp (tApp ListNat.append (tVar 1)) (tVar 0)).

Definition t_plus_lens : tm :=
  tApp (tApp Examples.plusL (tApp ListNat.length (tVar 1)))
       (tApp ListNat.length (tVar 0)).

Definition residual_len_append : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_ll t_len_append Examples.nat_ty.

Definition residual_plus_lens : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_ll t_plus_lens Examples.nat_ty.

Lemma residualisation_length_append_plus_exact :
  residual_len_append = residual_plus_lens.
Proof.
  unfold residual_len_append, residual_plus_lens.
  vm_compute.
  reflexivity.
Qed.

Lemma residual_vec_index_append_plus_exact :
  option_map vec_ty_sc residual_len_append = option_map vec_ty_sc residual_plus_lens.
Proof.
  rewrite residualisation_length_append_plus_exact.
  reflexivity.
Qed.

(** Append associativity as an index.

    This is the classic "context reassociation" problem:
      length ((l1 ++ l2) ++ l3) == length (l1 ++ (l2 ++ l3))
*)

Definition Γ_lll : Ty.ctx := [ListNat.list_ty; ListNat.list_ty; ListNat.list_ty].

Definition t_len_append_assoc_l : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append
            (tApp (tApp ListNat.append (tVar 2)) (tVar 1)))
          (tVar 0)).

Definition t_len_append_assoc_r : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append (tVar 2))
          (tApp (tApp ListNat.append (tVar 1)) (tVar 0))).

Definition residual_len_append_assoc_l : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_lll t_len_append_assoc_l Examples.nat_ty.

Definition residual_len_append_assoc_r : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_lll t_len_append_assoc_r Examples.nat_ty.

(**
  Append associativity: a 2-pass supercompilation normal form.

  One pass of residualisation still leaves a representation-dependent structure.
  Re-running supercompilation on the residual term collapses the two variants to
  definitional equality.

  (This is a standard phenomenon: supercompilation is not necessarily
  idempotent in one pass unless the residualiser is SCC-canonical.)
*)

Definition residual_len_append_assoc_l_fp : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ_listnat Γ_lll t_len_append_assoc_l Examples.nat_ty.

Definition residual_len_append_assoc_r_fp : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ_listnat Γ_lll t_len_append_assoc_r Examples.nat_ty.

Lemma residualisation_length_append_assoc_fp_exact :
  residual_len_append_assoc_l_fp = residual_len_append_assoc_r_fp.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma residual_vec_index_append_assoc_fp_exact :
  option_map vec_ty_sc residual_len_append_assoc_l_fp = option_map vec_ty_sc residual_len_append_assoc_r_fp.
Proof.
  rewrite residualisation_length_append_assoc_fp_exact.
  reflexivity.
Qed.

Lemma residualisation_length_append_assoc_smoke :
  exists t1 t2,
    residual_len_append_assoc_l = Some t1 /\ residual_len_append_assoc_r = Some t2.
Proof.
  unfold residual_len_append_assoc_l, residual_len_append_assoc_r.
  do 2 eexists.
  split; vm_compute; reflexivity.
Qed.

(** Take/drop context splitting as an index.

    length (take n l ++ drop n l) == length l
*)

Definition Γ_ln : Ty.ctx := [ListNat.list_ty; Examples.nat_ty].

Definition t_len_take_drop : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.append
            (tApp (tApp ListNat.take (tVar 1)) (tVar 0)))
          (tApp (tApp ListNat.drop (tVar 1)) (tVar 0))).

Definition t_len_l : tm := tApp ListNat.length (tVar 0).

Definition residual_len_take_drop : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_ln t_len_take_drop Examples.nat_ty.

Definition residual_len_l : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_ln t_len_l Examples.nat_ty.

Lemma residualisation_length_take_drop_smoke :
  exists t1 t2, residual_len_take_drop = Some t1 /\ residual_len_l = Some t2.
Proof.
  unfold residual_len_take_drop, residual_len_l.
  do 2 eexists.
  split; vm_compute; reflexivity.
Qed.

(** A slightly larger pipeline: [length (map f (map g l))] is also deforested. *)

Definition Γ_listnat2 : Ty.ctx := [ListNat.list_ty; ListNat.nat2nat; ListNat.nat2nat].

Definition t_len_map_map : tm :=
  tApp ListNat.length
    (tApp (tApp ListNat.map (tVar 1))
      (tApp (tApp ListNat.map (tVar 2)) (tVar 0))).

Definition t_len2 : tm := tApp ListNat.length (tVar 0).

Definition residual_len_map_map : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_listnat2 t_len_map_map Examples.nat_ty.

Definition residual_len2 : option tm :=
  Supercompile.residualise_jTy 80 200 Σ_listnat Γ_listnat2 t_len2 Examples.nat_ty.

(**
  NOTE: at the moment, the supercompiler does not yet automatically fuse the
  nested map-map pattern for this example (so we do not get exact equality
  between these two residuals).

  This is a useful regression test: once we strengthen the whistle/generalisation
  control further, we should be able to upgrade this to an exact-equality lemma.
*)

Lemma residualisation_length_map_map_smoke :
  exists t1 t2, residual_len_map_map = Some t1 /\ residual_len2 = Some t2.
Proof.
  unfold residual_len_map_map, residual_len2.
  do 2 eexists.
  split; vm_compute; reflexivity.
Qed.
