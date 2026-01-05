From Stdlib Require Import List Arith Lia PeanoNat Utf8 FunctionalExtensionality.
From stdpp Require Import prelude countable.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Preproof Require Import Preproof.

Import ListNotations.

Set Default Proof Using "Type".

Module Typing.
  Module SP := StrictPos.
  Module T := Term.Syntax.

  Definition ctx : Type := list T.tm.
  Definition env : Type := list (SP.ind_sig T.tm).

  (* Telescope contexts with shift-aware lookup. *)
  Fixpoint ctx_lookup (Γ : ctx) (x : nat) : option T.tm :=
    match Γ, x with
    | [], _ => None
    | A :: _, 0 => Some (T.shift 1 0 A)
    | _ :: Γ, S x => option_map (T.shift 1 0) (ctx_lookup Γ x)
    end.

  Definition ctx_extend (Γ : ctx) (A : T.tm) : ctx := A :: Γ.

  Lemma ctx_lookup_lt (Γ : ctx) (x : nat) (A : T.tm) :
    ctx_lookup Γ x = Some A -> x < length Γ.
  Proof.
    revert x A.
    induction Γ as [|B Γ IH]; intros [|x] A H; simpl in *.
    - discriminate.
    - discriminate.
    - (* x = 0 *)
      inversion H.
      simpl.
      lia.
    - (* x = S x *)
      destruct (ctx_lookup Γ x) as [A'|] eqn:Hx; simpl in H.
      + inversion H.
        specialize (IH x A' Hx).
        simpl.
        lia.
      + discriminate.
  Qed.

  Lemma ctx_lookup_app_r (Γ Δ : ctx) (x : nat) :
    x < length Γ -> ctx_lookup (Γ ++ Δ) x = ctx_lookup Γ x.
  Proof.
    revert x.
    induction Γ as [|A Γ IH]; intros x Hx; simpl in *.
    - destruct x; [lia|].
      exfalso; lia.
    - destruct x as [|x].
      + reflexivity.
      + rewrite IH by lia.
        reflexivity.
  Qed.

  Fixpoint mk_pis (As : list T.tm) (B : T.tm) : T.tm :=
    match As with
    | [] => B
    | A :: As => T.tPi A (mk_pis As B)
    end.

  Inductive has_type (Σenv : env) : ctx -> T.tm -> T.tm -> Prop :=
  | ty_var Γ x A :
      ctx_lookup Γ x = Some A ->
      has_type Σenv Γ (T.tVar x) A

  | ty_sort Γ i :
      has_type Σenv Γ (T.tSort i) (T.tSort (S i))

  | ty_pi Γ A B i j :
      has_type Σenv Γ A (T.tSort i) ->
      has_type Σenv (ctx_extend Γ A) B (T.tSort j) ->
      has_type Σenv Γ (T.tPi A B) (T.tSort (Nat.max i j))

  | ty_lam Γ A t B i :
      has_type Σenv Γ A (T.tSort i) ->
      has_type Σenv (ctx_extend Γ A) t B ->
      has_type Σenv Γ (T.tLam A t) (T.tPi A B)

  | ty_app Γ t u A B :
      has_type Σenv Γ t (T.tPi A B) ->
      has_type Σenv Γ u A ->
      has_type Σenv Γ (T.tApp t u) (T.subst0 u B)

  | ty_fix Γ A t i :
      has_type Σenv Γ A (T.tSort i) ->
      has_type Σenv (ctx_extend Γ A) t (T.shift 1 0 A) ->
      has_type Σenv Γ (T.tFix A t) A

  | ty_ind Γ I ΣI :
      SP.lookup_ind Σenv I = Some ΣI ->
      has_type Σenv Γ (T.tInd I) (T.tSort (S (@SP.ind_level _ ΣI)))

  | ty_roll Γ I ΣI c ctor params recs :
      SP.lookup_ind Σenv I = Some ΣI ->
      SP.lookup_ctor ΣI c = Some ctor ->
      Forall2 (has_type Σenv Γ) params (@SP.ctor_param_tys _ ctor) ->
      Forall (fun r => has_type Σenv Γ r (T.tInd I)) recs ->
      length recs = (@SP.ctor_rec_arity _ ctor) ->
      has_type Σenv Γ (T.tRoll I c params recs) (T.tInd I)

  | ty_case Γ I ΣI scrut C brs i :
      SP.lookup_ind Σenv I = Some ΣI ->
      length brs = length (@SP.ind_ctors _ ΣI) ->
      has_type Σenv Γ scrut (T.tInd I) ->
      has_type Σenv Γ C (T.tSort i) ->
      (forall c ctor,
        SP.lookup_ctor ΣI c = Some ctor ->
        exists br,
          T.branch brs c = Some br
          /\ has_type Σenv Γ br
              (mk_pis (@SP.ctor_param_tys _ ctor ++ repeat (T.tInd I) (@SP.ctor_rec_arity _ ctor)) C)) ->
      has_type Σenv Γ (T.tCase I scrut C brs) C.

  Lemma branch_exists {ΣI : SP.ind_sig T.tm} (brs : list T.tm) (c : nat) (ctor : SP.ctor_sig T.tm) :
    length brs = length (@SP.ind_ctors _ ΣI) ->
    SP.lookup_ctor ΣI c = Some ctor ->
    exists br, T.branch brs c = Some br.
  Proof.
    intros Hlen Hctor.
    pose proof (SP.lookup_ctor_lt _ _ _ Hctor) as Hlt.
    rewrite <- Hlen in Hlt.
    destruct (nth_error brs c) as [br|] eqn:Hbr.
    - exists br. exact Hbr.
    - exfalso.
      apply nth_error_None in Hbr.
      lia.
  Qed.

  Lemma has_type_weaken_tail (Σenv : env) (Γ : ctx) (t A B : T.tm) :
    has_type Σenv Γ t A -> has_type Σenv (Γ ++ [B]) t A.
  Proof.
    revert Γ t A B.
    refine (fix IH Γ t A B (Hty : has_type Σenv Γ t A) {struct Hty}
            : has_type Σenv (Γ ++ [B]) t A := _).
    destruct Hty.
    - (* var *)
      apply ty_var.
      pose proof (ctx_lookup_lt Γ x A H) as Hlt.
      rewrite (ctx_lookup_app_r Γ [B] x Hlt).
      exact H.
    - (* sort *)
      constructor.
    - (* pi *)
      econstructor.
      + eapply IH; eauto.
      + match goal with
        | |- has_type _ (ctx_extend (_ ++ [_]) _) ?t ?Ty =>
            change (has_type Σenv ((ctx_extend Γ A) ++ [B]) t Ty)
        end.
        eapply IH; eauto.
    - (* lam *)
      econstructor.
      + eapply IH; eauto.
      + match goal with
        | |- has_type _ (ctx_extend (_ ++ [_]) _) ?t ?Ty =>
            change (has_type Σenv ((ctx_extend Γ A) ++ [B]) t Ty)
        end.
        eapply IH; eauto.
    - (* app *)
      econstructor.
      + eapply IH; eauto.
      + eapply IH; eauto.
    - (* fix *)
      econstructor.
      + eapply IH; eauto.
      + match goal with
        | |- has_type _ (ctx_extend (_ ++ [_]) _) ?t ?Ty =>
            change (has_type Σenv ((ctx_extend Γ A) ++ [B]) t Ty)
        end.
        eapply IH; eauto.
    - (* ind *)
      econstructor; eauto.
    - (* roll *)
      eapply ty_roll; try eassumption.
      + (* params *)
        match goal with
        | [ Hp : Forall2 (has_type Σenv Γ) ?ps ?tys
          |- Forall2 (has_type Σenv (Γ ++ [B])) ?ps ?tys ] =>
            clear -IH B Hp;
            induction Hp; constructor; eauto using IH
        end.
      + (* recs *)
        match goal with
        | [ Hr : Forall (fun r : T.tm => has_type Σenv Γ r (T.tInd I)) ?rs
          |- Forall (fun r : T.tm => has_type Σenv (Γ ++ [B]) r (T.tInd I)) ?rs ] =>
            clear -IH B Hr;
            induction Hr; constructor; eauto using IH
        end.
    - (* case *)
      eapply ty_case; try eassumption.
      + eapply IH; eauto.
      + eapply IH; eauto.
      + intros c ctor0 Hctor.
        match goal with
        | [ Hbrs : forall c1 ctor1,
              SP.lookup_ctor _ c1 = Some ctor1 ->
              exists br,
                T.branch _ c1 = Some br /\ has_type Σenv Γ br _
          |- _ ] =>
            destruct (Hbrs c ctor0 Hctor) as [br [Hbr Htybr]];
            exists br;
            split; [exact Hbr|];
            exact (IH _ _ _ B Htybr)
        end.
  Qed.

  (* Binder-stable explicit substitutions: (k, σ). *)

  Definition sub : Type := nat * list T.tm.

  Definition sub_k (s : sub) : nat := fst s.
  Definition sub_list (s : sub) : list T.tm := snd s.

  Definition sub_fun (s : sub) : nat -> T.tm :=
    fun x =>
      match nth_error (sub_list s) x with
      | Some u => u
      | None => T.tVar (x - length (sub_list s) + sub_k s)
      end.

  Definition subst_sub (s : sub) (t : T.tm) : T.tm := T.subst (sub_fun s) t.

  Definition up_sub (s : sub) : sub :=
    (S (sub_k s), T.tVar 0 :: map (T.rename (Autosubst_Basics.lift 1)) (sub_list s)).

  Lemma sub_fun_up (s : sub) :
    sub_fun (up_sub s) = T.up (sub_fun s).
  Proof.
    apply functional_extensionality; intros [|x]; simpl.
    - reflexivity.
    - unfold sub_fun.
      simpl.
      destruct (nth_error (sub_list s) x) as [u|] eqn:Hx.
      + rewrite nth_error_map, Hx.
        simpl.
        unfold T.up, Autosubst_Classes.up.
        simpl.
        rewrite Hx.
        simpl.
        reflexivity.
      + rewrite nth_error_map, Hx.
        simpl.
        unfold T.up, Autosubst_Classes.up.
        simpl.
        rewrite Hx.
        simpl.
        f_equal.
        rewrite length_map.
        lia.
  Qed.

  (* Convenience: cyclic proofs store just the argument list (k = 0). *)
  Definition subst_list (σ : list T.tm) (t : T.tm) : T.tm :=
    subst_sub (0, σ) t.

  Definition up_list (σ : list T.tm) : list T.tm :=
    sub_list (up_sub (0, σ)).

  (* Typed explicit substitutions (still list-backed). *)
  Inductive has_subst (Σenv : env) (Δ : ctx) : list T.tm -> ctx -> Prop :=
  | sub_nil :
      has_subst Σenv Δ [] []

  | sub_cons Γ A σ u :
      has_subst Σenv Δ σ Γ ->
      has_type Σenv Δ u (subst_list σ (T.shift 1 0 A)) ->
      has_subst Σenv Δ (u :: σ) (A :: Γ).

  Lemma has_subst_length (Σenv : env) (Δ : ctx) (σ : list T.tm) (Γ : ctx) :
    has_subst Σenv Δ σ Γ -> length σ = length Γ.
  Proof.
    intro Hs.
    induction Hs.
    - reflexivity.
    - simpl. now rewrite IHHs.
  Qed.

  Lemma has_subst_weaken_tail (Σenv : env) (Δ : ctx) (σ : list T.tm) (Γ : ctx) (B : T.tm) :
    has_subst Σenv Δ σ Γ -> has_subst Σenv (Δ ++ [B]) σ Γ.
  Proof.
    intro Hs.
    induction Hs.
    - constructor.
    - econstructor.
      + exact IHHs.
      + (* weaken the typing premise in the target context *)
        eapply has_type_weaken_tail.
        exact H.
  Qed.

  (* Substitution/renaming algebra (Autosubst-powered).

     These lemmas are the main ingredients needed later for renaming and
     substitution-preserves-typing proofs.
  *)

  Lemma shift1_eq_rename (t : T.tm) :
    T.shift 1 0 t = T.rename (fun x => x + 1) t.
  Proof.
    unfold T.shift, Term.Syntax.shift.
    assert (H : Term.Syntax.shift_sub 1 0 = fun x => x + 1).
    { apply functional_extensionality; intro x.
      unfold Term.Syntax.shift_sub.
      destruct (x <? 0) eqn:Hx.
      - apply Nat.ltb_lt in Hx. lia.
      - reflexivity. }
    now rewrite H.
  Qed.

  Lemma subst_comp_tm (sigma tau : var -> T.tm) (t : T.tm) :
    t.[sigma].[tau] = t.[sigma >> tau].
  Proof.
    apply subst_comp.
  Qed.

  Lemma subst0_comp_tm (t u v : T.tm) :
    (t.[u/]).[v/] = t.[u.[v/], v/].
  Proof.
    change (t.[u .: T.ids].[v .: T.ids] = t.[(u.[v/]) .: v .: T.ids]).
    rewrite subst_comp.
    assert (H : (u .: T.ids) >> (v .: T.ids) = (u.[v/]) .: v .: T.ids).
    { apply functional_extensionality; intros [|x]; simpl.
      - reflexivity.
      - destruct x; reflexivity. }
    now rewrite H.
  Qed.

  Module Cyclic.
    Inductive judgement : Type :=
    | jTy (Γ : ctx) (t A : T.tm)
    | jEq (Γ : ctx) (t u A : T.tm)
    | jSub (Δ : ctx) (s : sub) (Γ : ctx).

    Definition jTy_params (Γ : ctx) (ps As : list T.tm) : list judgement :=
      map (fun '(p, A) => jTy Γ p A) (combine ps As).

    Definition jTy_recs (Γ : ctx) (I : nat) (recs : list T.tm) : list judgement :=
      map (fun r => jTy Γ r (T.tInd I)) recs.

    Definition branch_ty (I : nat) (ctor : SP.ctor_sig T.tm) (C : T.tm) : T.tm :=
      mk_pis (@SP.ctor_param_tys _ ctor ++ repeat (T.tInd I) (@SP.ctor_rec_arity _ ctor)) C.

    Definition jTy_branches (Γ : ctx) (I : nat) (ΣI : SP.ind_sig T.tm) (C : T.tm) (brs : list T.tm) : list judgement :=
      map (fun '(ctor, br) => jTy Γ br (branch_ty I ctor C)) (combine (@SP.ind_ctors _ ΣI) brs).

    Definition rule (Σenv : env) (j : judgement) (premises : list judgement) : Prop :=
      match j with
      | jSub Δ (k, []) [] => premises = []
      | jSub Δ (k, u :: σ) (A :: Γ) =>
          premises = [jSub Δ (k, σ) Γ; jTy Δ u (subst_sub (k, σ) (T.shift 1 0 A))]
      | jSub _ _ _ => False

      | jTy Γ (T.tVar x) A => premises = [] ∧ ctx_lookup Γ x = Some A
      | jTy Γ (T.tSort i) (T.tSort k) => premises = [] ∧ k = S i

      | jTy Γ (T.tPi A B) (T.tSort k) =>
          exists i j,
            k = Nat.max i j ∧
            premises = [jTy Γ A (T.tSort i); jTy (ctx_extend Γ A) B (T.tSort j)]

      | jTy Γ (T.tLam A t) (T.tPi A' B) =>
          exists i,
            A' = A ∧
            premises = [jTy Γ A (T.tSort i); jTy (ctx_extend Γ A) t B]

      | jTy Γ (T.tApp t u) Ty =>
          exists A B,
            Ty = T.subst0 u B ∧
            premises = [jTy Γ t (T.tPi A B); jTy Γ u A]

      | jTy Γ (T.tFix A t) Ty =>
          exists i,
            Ty = A ∧
            premises = [jTy Γ A (T.tSort i); jTy (ctx_extend Γ A) t (T.shift 1 0 A)]

      | jTy Γ (T.tInd ind) (T.tSort k) =>
          exists ΣI,
            premises = []
            /\ SP.lookup_ind Σenv ind = Some ΣI
            /\ k = S (@SP.ind_level _ ΣI)

      | jTy Γ (T.tRoll ind c params recs) (T.tInd ind') =>
          exists ΣI ctor,
            ind' = ind
            /\ SP.lookup_ind Σenv ind = Some ΣI
            /\ SP.lookup_ctor ΣI c = Some ctor
            /\ length params = length (@SP.ctor_param_tys _ ctor)
            /\ length recs = (@SP.ctor_rec_arity _ ctor)
            /\ premises = jTy_params Γ params (@SP.ctor_param_tys _ ctor) ++ jTy_recs Γ ind recs

      | jTy Γ (T.tCase ind scrut C brs) Ty =>
          exists i ΣI,
            Ty = C
            /\ SP.lookup_ind Σenv ind = Some ΣI
            /\ length brs = length (@SP.ind_ctors _ ΣI)
            /\ premises = [jTy Γ scrut (T.tInd ind); jTy Γ C (T.tSort i)] ++ jTy_branches Γ ind ΣI C brs

      | jTy _ _ _ => False

      | jEq Γ t u A =>
          (t = u ∧ premises = [jTy Γ t A])
          ∨ (premises = [jEq Γ u t A])
          ∨ (exists m, premises = [jEq Γ t m A; jEq Γ m u A])
          ∨ (step t u ∧ premises = [jTy Γ t A; jTy Γ u A])
      end
      ∨
      match j with
      | jTy Γ t A =>
          exists Γ0 t0 A0 s,
            premises = [jTy Γ0 t0 A0; jSub Γ s Γ0] ∧
            t = subst_sub s t0 ∧
            A = subst_sub s A0
      | jEq Γ t u A =>
          exists Γ0 t0 u0 A0 s,
            premises = [jEq Γ0 t0 u0 A0; jSub Γ s Γ0] ∧
            t = subst_sub s t0 ∧
            u = subst_sub s u0 ∧
            A = subst_sub s A0
      | jSub _ _ _ => False
      end.

    Definition preproof (Σenv : env) {V : Type} `{EqDecision V} `{Countable V} : Type :=
      Preproof.preproof (Judgement := judgement) (rule Σenv) (V := V).

    Definition rooted_preproof (Σenv : env) {V : Type} `{EqDecision V} `{Countable V} : Type :=
      Preproof.rooted_preproof (Judgement := judgement) (rule Σenv) (V := V).
  End Cyclic.

  Module CyclicTerm.
    Inductive ctm : Type :=
    | cVar (x : nat)
    | cSort (i : nat)
    | cPi (A : ctm) (B : ctm)
    | cLam (A : ctm) (t : ctm)
    | cApp (t u : ctm)
    | cFix (A : ctm) (t : ctm)
    | cInd (ind : nat)
    | cRoll (ind : nat) (ctor : nat) (params recs : list ctm)
    | cCase (ind : nat) (scrut : ctm) (C : ctm) (brs : list ctm)
    | cBack (args : list ctm).

    Fixpoint apps (t : T.tm) (us : list T.tm) : T.tm :=
      match us with
      | [] => t
      | u :: us => apps (T.tApp t u) us
      end.

    Fixpoint erase (t : ctm) : T.tm :=
      match t with
      | cVar x => T.tVar x
      | cSort i => T.tSort i
      | cPi A B => T.tPi (erase A) (erase B)
      | cLam A t => T.tLam (erase A) (erase t)
      | cApp t u => T.tApp (erase t) (erase u)
      | cFix A t => T.tFix (erase A) (erase t)
      | cInd ind => T.tInd ind
      | cRoll ind ctor ps rs => T.tRoll ind ctor (map erase ps) (map erase rs)
      | cCase ind scrut C brs => T.tCase ind (erase scrut) (erase C) (map erase brs)
      | cBack args => apps (T.tVar 0) (map erase args)
      end.
  End CyclicTerm.
End Typing.
