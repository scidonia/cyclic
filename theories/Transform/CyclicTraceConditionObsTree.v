From Stdlib Require Import List Arith Lia Utf8 Relations Wellfounded.

From Cyclic.Transform Require Import SequentObservationRules.

Import ListNotations.

Set Default Proof Using "Type".

Module SOR := SequentObservationRules.

(** Well-founded descent on observation trees.

    This is a small, reusable component for cyclic trace conditions: whenever a
    trace step chooses a recursive observation subtree of a constructor node, we
    can justify a strict decrease using the size of observation trees.
*)

Fixpoint obs_size (o : SOR.obs_tree) : nat :=
  match o with
  | SOR.obsCtor _ recs =>
      S (fold_right (fun o acc => obs_size o + acc) 0 recs)
  end.

Definition obs_forest_size (os : list SOR.obs_tree) : nat :=
  fold_right (fun o acc => obs_size o + acc) 0 os.

Definition lt_obs (o' o : SOR.obs_tree) : Prop := obs_size o' < obs_size o.

Lemma lt_obs_wf : well_founded lt_obs.
Proof.
  unfold lt_obs.
  eapply (wf_inverse_image _ _ lt obs_size).
  exact lt_wf.
Qed.

Lemma obs_size_le_forest_of_in (os : list SOR.obs_tree) (o : SOR.obs_tree) :
  In o os -> obs_size o <= obs_forest_size os.
Proof.
  unfold obs_forest_size.
  induction os as [|o0 os IH]; cbn; intro Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + lia.
    + specialize (IH Hin). lia.
Qed.

Lemma lt_obs_of_in_recs (c : nat) (recs : list SOR.obs_tree) (o : SOR.obs_tree) :
  In o recs -> lt_obs o (SOR.obsCtor c recs).
Proof.
  intro Hin.
  unfold lt_obs.
  cbn.
  pose proof (obs_size_le_forest_of_in recs o Hin) as Hle.
  unfold obs_forest_size in Hle.
  lia.
Qed.

(** Lift the observation-tree order to optional trace states.

    - [None] represents the absence of an active trace and has no predecessors.
    - [Some o] orders by strict decrease on [o].
*)
Definition lt_trace (τ' τ : option SOR.obs_tree) : Prop :=
  match τ, τ' with
  | Some o, Some o' => lt_obs o' o
  | _, _ => False
  end.

Lemma lt_trace_wf : well_founded lt_trace.
Proof.
  intro τ.
  destruct τ as [o|].
  - revert o.
    refine (well_founded_induction_type lt_obs_wf (fun o => Acc lt_trace (Some o)) _).
    intros o IH.
    constructor.
    intros τ' Hlt.
    destruct τ' as [o'|]; [|contradiction].
    apply IH.
    exact Hlt.
  - constructor.
    intros τ' Hlt.
    contradiction.
Qed.
