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

  (* Helper: apply a list of arguments to a term *)
  Fixpoint apps (t : T.tm) (args : list T.tm) : T.tm :=
    match args with
    | [] => t
    | a :: args => apps (T.tApp t a) args
    end.

  (* Helper: split args into params and indices given arity counts *)
  Definition split_at {A : Type} (n : nat) (xs : list A) : list A * list A :=
    (firstn n xs, skipn n xs).


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
      has_type Σenv Γ (T.tInd I []) (T.tSort (S (SP.ind_level ΣI)))

  | ty_roll Γ I ΣI c ctor args params recs :
      SP.lookup_ind Σenv I = Some ΣI ->
      SP.lookup_ctor ΣI c = Some ctor ->
      split_at (SP.ctor_param_arity ctor) args = (params, recs) ->
      Forall2 (has_type Σenv Γ) params (SP.ctor_param_tys ctor) ->
      Forall (fun r => has_type Σenv Γ r (T.tInd I [])) recs ->
      length recs = SP.ctor_rec_arity ctor ->
      has_type Σenv Γ (T.tRoll I c args) (T.tInd I [])

  | ty_case Γ I ΣI scrut C brs i :
      SP.lookup_ind Σenv I = Some ΣI ->
      length brs = length (SP.ind_ctors ΣI) ->
      has_type Σenv Γ scrut (T.tInd I []) ->
      has_type Σenv (ctx_extend Γ (T.tInd I [])) C (T.tSort i) ->
      (forall c ctor,
        SP.lookup_ctor ΣI c = Some ctor ->
        exists br,
          T.branch brs c = Some br
          /\
          let As := SP.ctor_param_tys ctor ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor) in
          let m := length As in
          has_type Σenv Γ br
            (mk_pis As (C.[T.tRoll I c (map T.tVar (rev (seq 0 m))) .: ren (+m)]))) ->
      has_type Σenv Γ (T.tCase I scrut C brs) (T.subst0 scrut C).

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
        | [ Hr : Forall (fun r : T.tm => has_type Σenv Γ r (T.tInd I [])) ?rs
          |- Forall (fun r : T.tm => has_type Σenv (Γ ++ [B]) r (T.tInd I [])) ?rs ] =>
            clear -IH B Hr;
            induction Hr; constructor; eauto using IH
        end.
    - (* case *)
      eapply ty_case; try eassumption.
      + eapply IH; eauto.
      + (* motive C is typed under binder *)
        exact (IH (ctx_extend Γ (T.tInd I [])) C (T.tSort i) B Hty2).
      + intros c ctor0 Hctor.
        destruct (H1 c ctor0 Hctor) as [br [Hbr Htybr]].
        exists br.
        split; [exact Hbr|].
        exact (IH _ _ _ B Htybr).
  Qed.

  Lemma shift_sub_1_0_eq (x : var) : T.shift_sub 1 0 x = (+1) x.
  Proof.
    unfold T.shift_sub.
    destruct (x <? 0) eqn:H; [exfalso; apply (Nat.ltb_lt x 0) in H; lia|].
    change (x + 1) with (Nat.add x 1).
    rewrite Nat.add_comm. reflexivity.
  Qed.

  Lemma up_S_eq (σ : var -> T.tm) (x : var) :
    up σ (S x) = (σ x).[ren (+1)].
  Proof.
    unfold up, Autosubst_Classes.up.
    cbn.
    rewrite rename_subst.
    reflexivity.
  Qed.

  Lemma shift_up_type_eq (C : T.tm) (σ : var -> T.tm) :
    C.[σ].[ren (+1)] = (T.shift 1 0 C).[up σ].
  Proof.
    unfold T.shift, T.rename.
    rewrite !rename_subst, !subst_comp.
    apply (f_equal (fun (τ : var -> T.tm) => C.[τ])).
    extensionality x.
    unfold scomp. simpl.
    rewrite (shift_sub_1_0_eq x).
    symmetry. apply up_S_eq.
  Qed.

  Lemma shift_is_ren_subst (D : T.tm) : T.shift 1 0 D = D.[ren (+1)].
  Proof.
    unfold T.shift, T.rename.
    replace (Autosubst_Classes.rename (T.shift_sub 1 0) D) with (D.[ren (T.shift_sub 1 0)]).
    - apply (f_equal (fun τ : var -> T.tm => D.[τ])).
      apply functional_extensionality. intro z. cbn. f_equal. apply shift_sub_1_0_eq.
    - symmetry. apply rename_subst.
  Qed.

  Lemma shift_up_simpl (A : T.tm) (σ : var -> T.tm) :
    (T.shift 1 0 A).[up σ] = T.shift 1 0 (A.[σ]).
  Proof.
    rewrite shift_is_ren_subst, (shift_is_ren_subst (A.[σ])).
    rewrite !subst_comp.
    apply (f_equal (fun τ : var -> T.tm => A.[τ])).
    apply functional_extensionality. intro z. cbn. apply up_S_eq.
  Qed.

  (** Substitution lemma as a [Fixpoint]. *)
  Fixpoint has_type_subst (Σenv : env) (Γ Δ : ctx) (σ : var -> T.tm) (t A : T.tm)
      (Hty : has_type Σenv Γ t A) {struct Hty} :
      (forall x, match ctx_lookup Γ x with
        | Some C => has_type Σenv Δ (σ x) (C.[σ])
        | None => True
        end) ->
      has_type Σenv Δ (t.[σ]) (A.[σ]).
  Proof.
    intro Hsubst.
    destruct Hty as
      [Γ0 x A0 Hlk                                       (* ty_var *)
      |Γ0 i0                                              (* ty_sort *)
      |Γ0 A0 B0 i0 j0 Hty_pi1 Hty_pi2                      (* ty_pi *)
      |Γ0 A0 t0 B0 i0 Hty_lam1 Hty_lam2                    (* ty_lam *)
      |Γ0 t0 u0 A0 B0 Hty_app1 Hty_app2                    (* ty_app *)
      |Γ0 A0 t0 i0 Hty_fix1 Hty_fix2                       (* ty_fix *)
      |Γ0 I0 ΣI0 HlkI                                     (* ty_ind *)
      |Γ0 I0 ΣI0 c0 ctor0 args0 params0 recs0 HlkI' HlkC Hsplit Hpl Hrec Hlen
                                                           (* ty_roll *)
      |Γ0 I0 ΣI0 scrut0 C0 brs0 i0 HlkI'' HlenBrs Hty_scrut Hty_mot Hty_brs
                                                           (* ty_case *)
      ].
    - (* ty_var *) simpl. specialize (Hsubst x). rewrite Hlk in Hsubst. exact Hsubst.
    - (* ty_sort *) simpl. constructor.
    - (* ty_pi *) simpl.
      refine (ty_pi Σenv Δ (A0.[σ]) (B0.[up σ]) i0 j0 _ _).
      + apply (has_type_subst Σenv Γ0 Δ σ A0 (T.tSort i0) Hty_pi1 Hsubst).
      + apply (has_type_subst Σenv (ctx_extend Γ0 A0) (ctx_extend Δ A0.[σ]) (up σ) B0 (T.tSort j0) Hty_pi2).
        intros [|x]; simpl.
        * apply ty_var; simpl. rewrite shift_up_simpl. reflexivity.
        * destruct (ctx_lookup Γ0 x) as [C|] eqn:Hx; simpl.
          -- rewrite <- shift_up_type_eq, (up_S_eq σ x).
             pose proof (Hsubst x) as Hsx. rewrite Hx in Hsx.
             apply (has_type_subst Σenv Δ (ctx_extend Δ A0.[σ]) (ren (+1)) (σ x) (C.[σ]) Hsx).
             intros y; simpl. destruct (ctx_lookup Δ y) as [D|] eqn:Hy; simpl.
             ++ apply ty_var; simpl. rewrite Hy. simpl. f_equal. apply shift_is_ren_subst.
             ++ exact I.
          -- exact I.
    - (* ty_lam *) simpl.
      refine (ty_lam Σenv Δ (A0.[σ]) (t0.[up σ]) (B0.[up σ]) i0 _ _).
      + apply (has_type_subst Σenv Γ0 Δ σ A0 (T.tSort i0) Hty_lam1 Hsubst).
      + apply (has_type_subst Σenv (ctx_extend Γ0 A0) (ctx_extend Δ A0.[σ]) (up σ) t0 B0 Hty_lam2).
        intros [|x]; simpl.
        * apply ty_var; simpl. rewrite shift_up_simpl. reflexivity.
        * destruct (ctx_lookup Γ0 x) as [C|] eqn:Hx; simpl.
          -- rewrite <- shift_up_type_eq, (up_S_eq σ x).
             pose proof (Hsubst x) as Hsx. rewrite Hx in Hsx.
             apply (has_type_subst Σenv Δ (ctx_extend Δ A0.[σ]) (ren (+1)) (σ x) (C.[σ]) Hsx).
             intros y; simpl. destruct (ctx_lookup Δ y) as [D|] eqn:Hy; simpl.
             ++ apply ty_var; simpl. rewrite Hy. simpl. f_equal. apply shift_is_ren_subst.
             ++ exact I.
          -- exact I.
    - (* ty_app *)
      simpl. replace ((T.subst0 u0 B0).[σ]) with (T.subst0 (u0.[σ]) (B0.[up σ]))
        by (unfold T.subst0; asimpl; reflexivity).
      refine (ty_app Σenv Δ (t0.[σ]) (u0.[σ]) (A0.[σ]) (B0.[up σ]) _ _).
      + apply (has_type_subst Σenv Γ0 Δ σ t0 (T.tPi A0 B0) Hty_app1 Hsubst).
      + apply (has_type_subst Σenv Γ0 Δ σ u0 A0 Hty_app2 Hsubst).
     - (* ty_fix *) simpl.
      refine (ty_fix Σenv Δ (A0.[σ]) (t0.[up σ]) i0 _ _).
      + apply (has_type_subst Σenv Γ0 Δ σ A0 (T.tSort i0) Hty_fix1 Hsubst).
      + rewrite <- shift_up_simpl.
        apply (has_type_subst Σenv (ctx_extend Γ0 A0) (ctx_extend Δ A0.[σ]) (up σ) t0 (T.shift 1 0 A0) Hty_fix2).
        intros [|x]; simpl.
        * apply ty_var; simpl. rewrite shift_up_simpl. reflexivity.
        * destruct (ctx_lookup Γ0 x) as [C|] eqn:Hx; simpl;
          [ | exact I ].
          rewrite <- shift_up_type_eq, (up_S_eq σ x).
          pose proof (Hsubst x) as Hsx. rewrite Hx in Hsx.
          apply (has_type_subst Σenv Δ (ctx_extend Δ A0.[σ]) (ren (+1)) (σ x) (C.[σ]) Hsx).
          intros y; simpl; destruct (ctx_lookup Δ y) as [D|] eqn:Hy; simpl;
          [ apply ty_var; simpl; rewrite Hy; simpl; f_equal; apply shift_is_ren_subst
          | exact I ].
    - (* ty_ind *) simpl. eapply ty_ind. eauto.
    - (* ty_roll *) simpl.
      apply (ty_roll Σenv Δ I0 ΣI0 c0 ctor0 (args0..[σ]) (params0..[σ]) (recs0..[σ])).
      + eassumption. + eassumption.
      + unfold split_at. rewrite !list_subst_as_map, !firstn_map, !skipn_map. injection Hsplit. intros Hp Hr. rewrite Hp, Hr. reflexivity.
      + induction Hpl as [|? ? ? ? H Hpl IHpl]; simpl; [ apply Forall2_nil
        | apply Forall2_cons; [ pose proof (has_type_subst Σenv Γ0 Δ σ _ _ H Hsubst) as Hx; asimpl in Hx; exact Hx
                               | apply IHpl] ].
      + induction Hrec as [|? ? H Hrec IHrec]; simpl; [ apply Forall_nil
        | apply Forall_cons; [ pose proof (has_type_subst Σenv Γ0 Δ σ _ _ H Hsubst) as Hx; asimpl in Hx; exact Hx
                               | apply IHrec] ].
      + rewrite length_map. exact Hlen.
    - (* ty_case *) simpl. asimpl.
      eapply ty_case; try eassumption.
      + exact HlenBrs. + eauto.
      + apply (has_type_subst Σenv Γ0 Δ σ scrut0 (T.tInd I0 []) Hty_scrut Hsubst).
      + intros c ctor Hctor. destruct (Hty_brs c ctor Hctor) as [br [Hbr Htybr]].
        exists br. split; [exact Hbr|]. eauto.
  Defined.

  (** Weakening at the head via [has_type_subst]. *)
  Lemma has_type_weaken_head (Σenv : env) (Γ : ctx) (t A B : T.tm) (Hty : has_type Σenv Γ t A) :
    has_type Σenv (B :: Γ) (T.shift 1 0 t) (T.shift 1 0 A).
  Proof.
    apply (has_type_subst Σenv Γ (B :: Γ) (ren (+1)) t A Hty).
    intros x; simpl; destruct (ctx_lookup Γ x) as [C|] eqn:Hctx.
    - apply ty_var; simpl. rewrite Hctx. reflexivity.
    - exact I.
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
      map (fun r => jTy Γ r (T.tInd I [])) recs.

    Definition branch_ty (I : nat) (ctor : SP.ctor_sig T.tm) (C : T.tm) : T.tm :=
      mk_pis (SP.ctor_param_tys ctor ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor)) C.

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

      | jTy Γ (T.tInd ind args) (T.tSort k) =>
          exists ΣI,
            premises = []
            /\ SP.lookup_ind Σenv ind = Some ΣI
            /\ args = []
            /\ k = S (SP.ind_level ΣI)

      | jTy Γ (T.tRoll ind c args) (T.tInd ind' args') =>
          exists ΣI ctor params recs,
            ind' = ind
            /\ args' = []
            /\ SP.lookup_ind Σenv ind = Some ΣI
            /\ SP.lookup_ctor ΣI c = Some ctor
            /\ split_at (SP.ctor_param_arity ctor) args = (params, recs)
            /\ length recs = SP.ctor_rec_arity ctor
            /\ premises = jTy_params Γ params (SP.ctor_param_tys ctor) ++ jTy_recs Γ ind recs

      | jTy Γ (T.tCase ind scrut C brs) Ty =>
          exists i ΣI,
            Ty = C
            /\ SP.lookup_ind Σenv ind = Some ΣI
            /\ length brs = length (SP.ind_ctors ΣI)
            /\ premises = [jTy Γ scrut (T.tInd ind []); jTy Γ C (T.tSort i)] ++ jTy_branches Γ ind ΣI C brs

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
      | cInd ind => T.tInd ind []
      | cRoll ind ctor ps rs => T.tRoll ind ctor (map erase ps ++ map erase rs)
      | cCase ind scrut C brs => T.tCase ind (erase scrut) (erase C) (map erase brs)
      | cBack args => apps (T.tVar 0) (map erase args)
      end.
  End CyclicTerm.
End Typing.
