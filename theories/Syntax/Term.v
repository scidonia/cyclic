From Stdlib Require Import List Arith Lia Utf8 FunctionalExtensionality Wellfounded Program.Equality.
From Stdlib.Vectors Require Import Fin Vector VectorSpec.

From Cyclic.Syntax Require Import StrictPos.

Import ListNotations.

Set Default Proof Using "Type".

Module Syntax.
  Inductive tm : Type :=
  | tVar (x : nat)
  | tSort (i : nat)
  | tPi (A : tm) (B : tm)
  | tLam (A : tm) (t : tm)
  | tApp (t u : tm)
  | tFix (A : tm) (t : tm)
  | tInd (I : nat)
  | tRoll (I : nat) (c : nat) (params recs : list tm)
  | tCase (I : nat) (n : nat) (scrut : tm) (C : tm) (brs : Vector.t tm n).

  Definition branch {n} (brs : Vector.t tm n) (k : Fin.t n) : tm :=
    Vector.nth brs k.

  Fixpoint shift (d : nat) (c : nat) (t : tm) : tm :=
    match t with
    | tVar x => if Nat.ltb x c then tVar x else tVar (x + d)
    | tSort i => tSort i
    | tPi A B => tPi (shift d c A) (shift d (S c) B)
    | tLam A t => tLam (shift d c A) (shift d (S c) t)
    | tApp t u => tApp (shift d c t) (shift d c u)
    | tFix A t => tFix (shift d c A) (shift d (S c) t)
    | tInd ind => tInd ind
    | tRoll ind ctor ps rs =>
        tRoll ind ctor (List.map (shift d c) ps) (List.map (shift d c) rs)
    | tCase ind n scrut C brs =>
        tCase ind n (shift d c scrut) (shift d c C) (Vector.map (shift d c) brs)
    end.

  Definition up (σ : nat -> tm) : nat -> tm :=
    fun x => match x with 0 => tVar 0 | S x => shift 1 0 (σ x) end.

  Fixpoint subst (σ : nat -> tm) (t : tm) : tm :=
    match t with
    | tVar x => σ x
    | tSort i => tSort i
    | tPi A B => tPi (subst σ A) (subst (up σ) B)
    | tLam A t => tLam (subst σ A) (subst (up σ) t)
    | tApp t u => tApp (subst σ t) (subst σ u)
    | tFix A t => tFix (subst σ A) (subst (up σ) t)
    | tInd ind => tInd ind
    | tRoll ind ctor ps rs =>
        tRoll ind ctor (List.map (subst σ) ps) (List.map (subst σ) rs)
    | tCase ind n scrut C brs =>
        tCase ind n (subst σ scrut) (subst σ C) (Vector.map (subst σ) brs)
    end.

  Definition subst0 (u : tm) (t : tm) : tm :=
    subst (fun x => match x with 0 => u | S x => tVar x end) t.

  Module Lemmas.
    Fixpoint sum_list (ns : list nat) : nat :=
      match ns with
      | [] => 0
      | n :: ns => n + sum_list ns
      end.

    Fixpoint sum_fin (n : nat) (f : Fin.t n -> nat) : nat :=
      match n as n0 return (Fin.t n0 -> nat) -> nat with
      | 0 => fun _ => 0
      | S n => fun f => f Fin.F1 + sum_fin n (fun k => f (Fin.FS k))
      end f.

    Fixpoint size (t : tm) : nat :=
      match t with
      | tVar _ => 1
      | tSort _ => 1
      | tPi A B => 1 + size A + size B
      | tLam A t => 1 + size A + size t
      | tApp t u => 1 + size t + size u
      | tFix A t => 1 + size A + size t
      | tInd _ => 1
      | tRoll _ _ ps rs => 1 + sum_list (List.map size ps) + sum_list (List.map size rs)
      | tCase _ n scrut C brs =>
          1 + size scrut + size C + sum_fin n (fun k => size (branch brs k))
      end.

    Definition wf_tm : well_founded (fun t1 t2 => size t1 < size t2) :=
      wf_inverse_image _ _ lt size Nat.lt_wf_0.

    Lemma size_le_sum_list {ps : list tm} {p : tm} :
      List.In p ps -> size p <= sum_list (List.map size ps).
    Proof.
      intro Hin.
      induction ps as [|q qs IH]; simpl in *.
      - contradiction.
      - destruct Hin as [Hin|Hin]; subst.
        + lia.
        + specialize (IH Hin).
          lia.
    Qed.

    Lemma size_lt_roll_param {I c} {params recs : list tm} {p : tm} :
      List.In p params -> size p < size (tRoll I c params recs).
    Proof.
      intro Hin.
      simpl.
      pose proof (size_le_sum_list (ps:=params) (p:=p) Hin) as Hle.
      lia.
    Qed.

    Lemma size_lt_roll_rec {I c} {params recs : list tm} {r : tm} :
      List.In r recs -> size r < size (tRoll I c params recs).
    Proof.
      intro Hin.
      simpl.
      pose proof (size_le_sum_list (ps:=recs) (p:=r) Hin) as Hle.
      lia.
    Qed.

    Lemma size_le_sum_fin {n} (brs : Vector.t tm n) (k : Fin.t n) :
      size (branch brs k) <= sum_fin n (fun j => size (branch brs j)).
    Proof.
      revert brs k.
      induction n as [|n IH]; intros brs k.
      - inversion k.
      - dependent destruction brs.
        dependent destruction k.
        + simpl. lia.
        + simpl.
          specialize (IH brs k).
          lia.
    Qed.

    Lemma size_lt_case_branch {I n} {scrut C : tm} {brs : Vector.t tm n} (k : Fin.t n) :
      size (branch brs k) < size (tCase I n scrut C brs).
    Proof.
      simpl.
      pose proof (size_le_sum_fin brs k) as Hle.
      lia.
    Qed.

    Definition shift_sub (d c : nat) : nat -> tm :=
      fun x => if Nat.ltb x c then tVar x else tVar (x + d).

    Lemma up_shift_sub d c : up (shift_sub d c) = shift_sub d (S c).
    Proof.
      apply functional_extensionality; intro x.
      destruct x as [|x]; simpl.
      - reflexivity.
      - unfold shift_sub.
        destruct (Nat.ltb x c) eqn:Hlt.
        + apply Nat.ltb_lt in Hlt.
          assert (Nat.ltb (S x) (S c) = true) as Hlt'.
          { apply Nat.ltb_lt. lia. }
          rewrite Hlt'.
          simpl.
          f_equal.
          lia.
        + apply Nat.ltb_ge in Hlt.
          assert (Nat.ltb (S x) (S c) = false) as Hge'.
          { apply Nat.ltb_ge. lia. }
          rewrite Hge'.
          simpl.
          f_equal.
          lia.
    Qed.

    Lemma up_ext (σ τ : nat -> tm) :
      (forall x, σ x = τ x) -> forall x, up σ x = up τ x.
    Proof.
      intro Heq.
      intro x.
      destruct x as [|x]; simpl; [reflexivity|].
      rewrite Heq.
      reflexivity.
    Qed.

    Lemma subst_ext (σ τ : nat -> tm) (t : tm) :
      (forall x, σ x = τ x) -> subst σ t = subst τ t.
    Proof.
      intro Heq.
      revert σ τ Heq.
      refine (well_founded_induction wf_tm
        (fun t => forall σ τ, (forall x, σ x = τ x) -> subst σ t = subst τ t)
        _ t).
      intros t0 IH σ τ Heq0.
      destruct t0 as
        [x|i|A B|A body|fn arg|A body|ind|ind ctor params recs|ind n scrut C brs];
        simpl; try reflexivity.
      - exact (Heq0 x).
      - f_equal.
        + assert (Hlt : size A < size (tPi A B)) by (simpl; lia).
          exact (IH A Hlt σ τ Heq0).
        + assert (Hlt : size B < size (tPi A B)) by (simpl; lia).
          exact (IH B Hlt (up σ) (up τ) (up_ext _ _ Heq0)).
      - f_equal.
        + assert (Hlt : size A < size (tLam A body)) by (simpl; lia).
          exact (IH A Hlt σ τ Heq0).
        + assert (Hlt : size body < size (tLam A body)) by (simpl; lia).
          exact (IH body Hlt (up σ) (up τ) (up_ext _ _ Heq0)).
      - f_equal.
        + assert (Hlt : size fn < size (tApp fn arg)) by (simpl; lia).
          exact (IH fn Hlt σ τ Heq0).
        + assert (Hlt : size arg < size (tApp fn arg)) by (simpl; lia).
          exact (IH arg Hlt σ τ Heq0).
      - f_equal.
        + assert (Hlt : size A < size (tFix A body)) by (simpl; lia).
          exact (IH A Hlt σ τ Heq0).
        + assert (Hlt : size body < size (tFix A body)) by (simpl; lia).
          exact (IH body Hlt (up σ) (up τ) (up_ext _ _ Heq0)).
      - f_equal.
        + apply List.map_ext_in.
          intros p Hp.
          pose proof (size_lt_roll_param (I:=ind) (c:=ctor) (params:=params) (recs:=recs) (p:=p) Hp) as Hlt.
          exact (IH p Hlt σ τ Heq0).
        + apply List.map_ext_in.
          intros r Hr.
          pose proof (size_lt_roll_rec (I:=ind) (c:=ctor) (params:=params) (recs:=recs) (r:=r) Hr) as Hlt.
          exact (IH r Hlt σ τ Heq0).
      - f_equal.
        + assert (Hlt : size scrut < size (tCase ind n scrut C brs)) by (simpl; lia).
          exact (IH scrut Hlt σ τ Heq0).
        + assert (Hlt : size C < size (tCase ind n scrut C brs)) by (simpl; lia).
          exact (IH C Hlt σ τ Heq0).
        + apply (proj1 (VectorSpec.eq_nth_iff _ _
            (Vector.map (subst σ) brs)
            (Vector.map (subst τ) brs))).
          intros p1 p2 Hp.
          subst p2.
          rewrite (VectorSpec.nth_map (subst σ) brs p1 p1 eq_refl).
          rewrite (VectorSpec.nth_map (subst τ) brs p1 p1 eq_refl).
          pose proof (size_lt_case_branch (I:=ind) (n:=n) (scrut:=scrut) (C:=C) (brs:=brs) p1) as Hlt.
          exact (IH (branch brs p1) Hlt σ τ Heq0).
    Qed.

    Lemma shift_as_subst (d c : nat) (t : tm) :
      shift d c t = subst (shift_sub d c) t.
    Proof.
      revert c.
      refine (well_founded_induction wf_tm
        (fun t => forall c, shift d c t = subst (shift_sub d c) t)
        _ t).
      intros t0 IH c0.
      destruct t0 as
        [x|i|A B|A body|fn arg|A body|ind|ind ctor params recs|ind n scrut C brs];
        simpl; try reflexivity.
      - apply f_equal2.
        + assert (Hlt : size A < size (tPi A B)) by (simpl; lia).
          exact (IH A Hlt c0).
        + rewrite up_shift_sub.
          assert (Hlt : size B < size (tPi A B)) by (simpl; lia).
          exact (IH B Hlt (S c0)).
      - apply f_equal2.
        + assert (Hlt : size A < size (tLam A body)) by (simpl; lia).
          exact (IH A Hlt c0).
        + rewrite up_shift_sub.
          assert (Hlt : size body < size (tLam A body)) by (simpl; lia).
          exact (IH body Hlt (S c0)).
      - apply f_equal2.
        + assert (Hlt : size fn < size (tApp fn arg)) by (simpl; lia).
          exact (IH fn Hlt c0).
        + assert (Hlt : size arg < size (tApp fn arg)) by (simpl; lia).
          exact (IH arg Hlt c0).
      - apply f_equal2.
        + assert (Hlt : size A < size (tFix A body)) by (simpl; lia).
          exact (IH A Hlt c0).
        + rewrite up_shift_sub.
          assert (Hlt : size body < size (tFix A body)) by (simpl; lia).
          exact (IH body Hlt (S c0)).
      - f_equal.
        + apply List.map_ext_in.
          intros p Hp.
          pose proof (size_lt_roll_param (I:=ind) (c:=ctor) (params:=params) (recs:=recs) (p:=p) Hp) as Hlt.
          exact (IH p Hlt c0).
        + apply List.map_ext_in.
          intros r Hr.
          pose proof (size_lt_roll_rec (I:=ind) (c:=ctor) (params:=params) (recs:=recs) (r:=r) Hr) as Hlt.
          exact (IH r Hlt c0).
      - apply f_equal3.
        + assert (Hlt : size scrut < size (tCase ind n scrut C brs)) by (simpl; lia).
          exact (IH scrut Hlt c0).
        + assert (Hlt : size C < size (tCase ind n scrut C brs)) by (simpl; lia).
          exact (IH C Hlt c0).
        + apply (proj1 (VectorSpec.eq_nth_iff _ _
            (Vector.map (shift d c0) brs)
            (Vector.map (subst (shift_sub d c0)) brs))).
          intros p1 p2 Hp.
          subst p2.
          rewrite (VectorSpec.nth_map (shift d c0) brs p1 p1 eq_refl).
          rewrite (VectorSpec.nth_map (subst (shift_sub d c0)) brs p1 p1 eq_refl).
          pose proof (size_lt_case_branch (I:=ind) (n:=n) (scrut:=scrut) (C:=C) (brs:=brs) p1) as Hlt.
          exact (IH (branch brs p1) Hlt c0).
    Qed.

    Lemma subst_shift0 (σ : nat -> tm) (t : tm) :
      subst (up σ) (shift 1 0 t) = shift 1 0 (subst σ t).
    Admitted.

    Lemma up_comp_subst (σ τ : nat -> tm) :
      forall x, up (fun y => subst σ (τ y)) x = subst (up σ) (up τ x).
    Proof.
      intro x.
      destruct x as [|x]; simpl; [reflexivity|].
      symmetry.
      apply (subst_shift0 σ (τ x)).
    Qed.

    Lemma subst_comp (σ τ : nat -> tm) (t : tm) :
      subst σ (subst τ t) = subst (fun x => subst σ (τ x)) t.
    Proof.
      revert σ τ.
      refine (well_founded_induction wf_tm
        (fun t => forall σ τ,
          subst σ (subst τ t) = subst (fun x => subst σ (τ x)) t)
        _ t).
      intros t0 IH σ τ.
      destruct t0 as
        [x|i|A B|A body|fn arg|A body|ind|ind ctor params recs|ind n scrut C brs];
        simpl; try reflexivity.
      - f_equal.
        + apply (IH A). simpl; lia. exact σ. exact τ.
        + rewrite (IH B). 2: (simpl; lia). 2: exact (up σ). 2: exact (up τ).
          apply subst_ext.
          intro x.
          symmetry.
          apply up_comp_subst.
      - f_equal.
        + apply (IH A). simpl; lia. exact σ. exact τ.
        + rewrite (IH body). 2: (simpl; lia). 2: exact (up σ). 2: exact (up τ).
          apply subst_ext.
          intro x.
          symmetry.
          apply up_comp_subst.
      - f_equal.
        + apply (IH fn). simpl; lia. exact σ. exact τ.
        + apply (IH arg). simpl; lia. exact σ. exact τ.
      - f_equal.
        + apply (IH A). simpl; lia. exact σ. exact τ.
        + rewrite (IH body). 2: (simpl; lia). 2: exact (up σ). 2: exact (up τ).
          apply subst_ext.
          intro x.
          symmetry.
          apply up_comp_subst.
      - f_equal.
        + apply List.map_ext_in.
          intros p Hp.
          apply (IH p).
          * apply size_lt_roll_param; exact Hp.
          * exact σ.
          * exact τ.
        + apply List.map_ext_in.
          intros r Hr.
          apply (IH r).
          * apply size_lt_roll_rec; exact Hr.
          * exact σ.
          * exact τ.
      - f_equal.
        + apply (IH scrut). simpl; lia. exact σ. exact τ.
        + apply (IH C). simpl; lia. exact σ. exact τ.
        + apply Vector.map_ext.
          intro k.
          apply (IH (branch brs k)).
          * apply size_lt_case_branch.
          * exact σ.
          * exact τ.
    Qed.
  End Lemmas.
End Syntax.
