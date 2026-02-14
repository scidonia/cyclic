From Stdlib Require Import List Utf8.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Equiv Require Import CIUNatObs.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.

(**
  Checklist example: extensional equality

    length (map f l) == length l

  in the sense of the Nat observation [terminates_to_nat] used by
  [Equiv.CIUNatObs].

  Note: because [tRoll] is a value regardless of its arguments in our CBN
  semantics, a direct value-observational CIU statement is too intensional:
  [length l] and [length (map f l)] produce different *syntactic* [succ]
  thunks. The Nat observation (numeral readback) is the intended notion.

  This file is meant to support the paper/checklist example; a full proof
  (by analysis of the operational semantics of [map] and [length]) remains TODO.
*)

Definition Σ_listnat : Ty.env := [Examples.Nat_sig; ListNat.List_sig].
Definition Γ_listnat : Ty.ctx := [ListNat.list_ty; ListNat.nat2nat].

(** Open terms in context Γ = [l : List; f : Nat→Nat]. *)
Definition t_len_map : tm :=
  tApp ListNat.length (tApp (tApp ListNat.map (tVar 1)) (tVar 0)).

Definition t_len : tm := tApp ListNat.length (tVar 0).

(** Closed observational equivalence for any (possibly open) f and l. *)
Theorem nat_obs_rel_length_map (f l : tm) :
  CIUNatObs.nat_obs_rel
    (tApp ListNat.length (tApp (tApp ListNat.map f) l))
    (tApp ListNat.length l).
Proof.
  (* TODO: prove via an extensional list-length observation and show
     [map] preserves the spine under call-by-name. *)
Admitted.

(** Judgement-level (typed-substitution) wrapper used by the CIU story. *)
Theorem ciu_jNatObs_length_map :
  CIUNatObs.ciu_jNatObs Σ_listnat Γ_listnat t_len_map t_len.
Proof.
  intros Δ σ Hσ _Hvσ n.
  (* Reduce to the closed lemma on the instantiated f and l.

     Here Γ has two variables, so any [has_subst] gives us a 2-element list σ.
  *)
  pose proof (Ty.has_subst_length _ _ _ _ Hσ) as Hlen.
  cbn [Γ_listnat] in Hlen.
  destruct σ as [|l [|f σ]]; simpl in Hlen; try discriminate.
  destruct σ as [|? ?]; [|discriminate].
  unfold t_len_map, t_len.
  unfold Ty.subst_list, Typing.Typing.subst_list, Ty.subst_sub, Typing.Typing.subst_sub.
  cbn [Typing.Typing.sub_fun].
  exact (nat_obs_rel_length_map f l n).
Qed.

(**
  Exact equality after supercompilation (term-level)

  The file `theories/Transform/Supercompile.v` now contains a term-level
  supercompiler driver `supercompile_tm` that performs *proper driving* according
  to the CBN semantics (β/iota/fix, plus scrutinee driving), and applies the
  generic CaseCase commuting conversion.

  This is the mechanism by which we expect deforestation/fusion to emerge, with
  no domain-specific rewrite laws.
*)

From Cyclic.Transform Require Import Supercompile.

Definition residual_len_map : option tm :=
  Supercompile.residualise_jTy 200 400 Σ_listnat Γ_listnat t_len_map Examples.nat_ty.

Definition residual_len : option tm :=
  Supercompile.residualise_jTy 200 400 Σ_listnat Γ_listnat t_len Examples.nat_ty.

Lemma residualisation_length_map_smoke :
  exists t1 t2, residual_len_map = Some t1 /\ residual_len = Some t2.
Proof.
  unfold residual_len_map, residual_len.
  (* This is just a sanity check that residualisation runs. *)
  do 2 eexists.
  split.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma residualisation_length_map_exact :
  residual_len_map = residual_len.
Proof.
  vm_compute.
  reflexivity.
Qed.
