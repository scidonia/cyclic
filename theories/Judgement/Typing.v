From Stdlib Require Import List Arith Lia PeanoNat Utf8 FunctionalExtensionality Wf_nat.
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

  | ty_roll Γ I ΣI c ctor args params recs (param_tys : list T.tm) :
      SP.lookup_ind Σenv I = Some ΣI ->
      SP.lookup_ctor ΣI c = Some ctor ->
      split_at (SP.ctor_param_arity ctor) args = (params, recs) ->
      param_tys = SP.ctor_param_tys ctor ->
      Forall2 (has_type Σenv Γ) params param_tys ->
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

  (** closed_param_tys: a well-formedness condition on the signature that
      says every constructor's parameter types are substitution-invariant.
      Required because [ty_roll] uses [ctor_param_tys] directly without
      applying the ambient substitution.  Non-parametric inductives satisfy
      this trivially; parametric ones with [tVar] entries do not.
      See discussion in the proof development notes. *)
  Definition closed_param_tys (Σenv : env) : Prop :=
    forall I ΣI c ctor (σ : var -> T.tm),
      SP.lookup_ind Σenv I = Some ΣI ->
      SP.lookup_ctor ΣI c = Some ctor ->
      (SP.ctor_param_tys ctor)..[σ] = SP.ctor_param_tys ctor.

  (* ----------------------------------------------------------------
     Helpers for the substitution proofs.
     ---------------------------------------------------------------- *)

  Lemma shift_sub_eq_S_new (x : var) : T.shift_sub 1 0 x = S x.
  Proof. unfold T.shift_sub. destruct (x <? 0) eqn:H; [apply Nat.ltb_lt in H; lia|lia]. Qed.

  Lemma shift_eq_ren_S (t : T.tm) : T.shift 1 0 t = t.[ren S].
  Proof.
    unfold T.shift, T.rename. rewrite rename_subst.
    apply (f_equal (fun τ => t.[τ])). extensionality x.
    unfold ren, T.shift_sub. simpl.
    destruct (x <? 0) eqn:H; [apply Nat.ltb_lt in H; lia|]. f_equal. lia.
  Qed.

  Lemma shift_up_eq_new (C : T.tm) (σ : var -> T.tm) :
    (T.shift 1 0 C).[T.up σ] = T.shift 1 0 (C.[σ]).
  Proof.
    unfold T.shift, T.rename. rewrite !rename_subst, !subst_comp.
    apply (f_equal (fun τ => C.[τ])). extensionality x.
    unfold scomp. simpl. rewrite shift_sub_eq_S_new.
    unfold T.up, Autosubst_Classes.up. simpl.
    unfold ids, Autosubst_Classes.ids, T.Ids_tm. rewrite rename_subst.
    apply (f_equal (fun τ => (σ x).[τ])). extensionality y.
    unfold scomp, T.shift_sub. simpl.
    destruct (y <? 0) eqn:Hy; [apply Nat.ltb_lt in Hy; lia|]. simpl. f_equal. lia.
  Qed.

  Lemma up_ren_eq_new (f : var -> var) :
    @up T.tm T.Ids_tm T.Rename_tm (ren f) = ren (upren f).
  Proof.
    apply functional_extensionality. intros [|x].
    - unfold up, Autosubst_Classes.up, upren. simpl. reflexivity.
    - unfold up, Autosubst_Classes.up, upren. simpl.
      unfold ids, Autosubst_Classes.ids, T.Ids_tm. reflexivity.
  Qed.

  Lemma subst0_ren_new (B u : T.tm) (f : var -> var) :
    (T.subst0 u B).[ren f] = T.subst0 (u.[ren f]) (B.[ren (upren f)]).
  Proof.
    unfold T.subst0. rewrite !subst_comp.
    apply (f_equal (fun τ => B.[τ])). extensionality x. unfold scomp, upren. simpl.
    destruct x as [|x]; simpl. reflexivity. reflexivity.
  Qed.

  Lemma mmap_firstn_new (n : nat) (σ : var -> T.tm) (xs : list T.tm) :
    firstn n xs..[σ] = (firstn n xs)..[σ].
  Proof.
    revert n. induction xs as [|a xs IH]; intros n.
    destruct n; reflexivity. destruct n as [|n]; simpl. reflexivity. f_equal. apply IH.
  Qed.

  Lemma mmap_skipn_new (n : nat) (σ : var -> T.tm) (xs : list T.tm) :
    skipn n xs..[σ] = (skipn n xs)..[σ].
  Proof.
    revert n. induction xs as [|a xs IH]; intros n.
    destruct n; reflexivity. destruct n as [|n]; simpl. reflexivity. apply IH.
  Qed.

  Lemma mmap_length_new (σ : var -> T.tm) (xs : list T.tm) : length xs..[σ] = length xs.
  Proof. induction xs; simpl. reflexivity. f_equal. exact IHxs. Qed.

  Lemma split_at_subst_new (n : nat) (σ : var -> T.tm) (args params recs : list T.tm) :
    split_at n args = (params, recs) ->
    split_at n args..[σ] = (params..[σ], recs..[σ]).
  Proof.
    unfold split_at. intro H. injection H as Hp Hr.
    rewrite <- Hp, <- Hr. rewrite mmap_firstn_new, mmap_skipn_new. reflexivity.
  Qed.

  Lemma upren_shift_sub_new (ξ : var -> var) (x : var) :
    upren ξ (T.shift_sub 1 0 x) = T.shift_sub 1 0 (ξ x).
  Proof.
    unfold T.shift_sub, upren.
    destruct (x <? 0) eqn:H; [apply Nat.ltb_lt in H; lia|].
    replace (x + 1) with (S x) by lia. simpl.
    destruct (ξ x <? 0) eqn:H2; [apply Nat.ltb_lt in H2; lia|]. f_equal. lia.
  Qed.

  Lemma shift_ren_upren_new (A : T.tm) (ξ : var -> var) :
    T.shift 1 0 (A.[ren ξ]) = (T.shift 1 0 A).[ren (upren ξ)].
  Proof.
    unfold T.shift, T.rename. rewrite !rename_subst, !subst_comp.
    apply (f_equal (fun τ => A.[τ])). extensionality x. unfold scomp. simpl.
    f_equal. symmetry. apply upren_shift_sub_new.
  Qed.

  Lemma ctx_lookup_ren_new (Γ : ctx) (f : var -> var) (Γ' : ctx) (A : T.tm) :
    (forall x C, ctx_lookup Γ x = Some C -> ctx_lookup Γ' (f x) = Some C.[ren f]) ->
    forall x C, ctx_lookup (A :: Γ) x = Some C ->
      ctx_lookup (A.[ren f] :: Γ') (upren f x) = Some C.[ren (upren f)].
  Proof.
    intros Hf [|x] C Hlookup.
    - simpl in Hlookup. inversion Hlookup; subst C. simpl. f_equal.
      exact (shift_ren_upren_new A f).
    - simpl in Hlookup.
      destruct (ctx_lookup Γ x) as [C'|] eqn:HC'; simpl in Hlookup; [|discriminate].
      inversion Hlookup; subst C. specialize (Hf x C' HC'). simpl. rewrite Hf. simpl.
      f_equal. exact (shift_ren_upren_new C' f).
  Qed.

  Lemma branch_subst_new (brs : list T.tm) (c : nat) (σ : var -> T.tm) (br : T.tm) :
    T.branch brs c = Some br -> T.branch brs..[σ] c = Some (br.[σ]).
  Proof.
    intro H. unfold T.branch. revert c H.
    induction brs as [|b brs IH]; intros c H.
    - destruct c; discriminate.
    - destruct c; simpl in H |- *.
      + inversion H; subst. reflexivity.
      + exact (IH c H).
  Qed.

  Lemma upn_up_eq_new (n : nat) (σ : var -> T.tm) : upn n (T.up σ) = upn (S n) σ.
  Proof. unfold upn. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

  Lemma upn_lt_fixed_new (m : nat) (σ : var -> T.tm) (i : var) :
    i < m -> upn m σ i = T.tVar i.
  Proof.
    revert i. induction m as [|m IH]; intro i.
    - intro H. lia.
    - intro H. destruct i as [|i].
      + unfold upn. simpl. unfold T.up, Autosubst_Classes.up. simpl. reflexivity.
      + unfold upn. simpl. unfold T.up, Autosubst_Classes.up. simpl.
        unfold ids, Autosubst_Classes.ids, T.Ids_tm.
        rewrite IH by lia. rewrite rename_subst. reflexivity.
  Qed.

  Lemma upn_ren_add_new (m : nat) (f : var -> var) (k : var) :
    upn m (ren f) (k + m) = T.tVar (f k + m).
  Proof.
    revert k. induction m as [|m IH]; intro k.
    - simpl. replace (k + 0) with k by lia. replace (f k + 0) with (f k) by lia. reflexivity.
    - replace (k + S m) with (S (k + m)) by lia.
      unfold upn. simpl. unfold T.up, Autosubst_Classes.up. simpl.
      unfold ids, Autosubst_Classes.ids, T.Ids_tm.
      rewrite IH. rewrite rename_subst. simpl.
      unfold ids, Autosubst_Classes.ids, T.Ids_tm. f_equal. lia.
  Qed.

  Lemma mmap_map_tVar_new (xs : list nat) (σ : var -> T.tm) :
    (map T.tVar xs)..[σ] = map (fun x => (T.tVar x).[σ]) xs.
  Proof. induction xs; simpl. reflexivity. f_equal. exact IHxs. Qed.

  Lemma tRoll_map_tVar_upn_new (I c m : nat) (σ : var -> T.tm) :
    (T.tRoll I c (map T.tVar (rev (seq 0 m)))).[upn m σ]
    = T.tRoll I c (map T.tVar (rev (seq 0 m))).
  Proof.
    simpl. f_equal. rewrite mmap_map_tVar_new. apply map_ext_in.
    intros x Hx. apply in_rev in Hx. apply in_seq in Hx.
    exact (upn_lt_fixed_new m σ x (proj2 Hx)).
  Qed.

  Lemma branch_body_subst_ren_new (I c m : nat) (C : T.tm) (f : var -> var) :
    (C.[T.tRoll I c (map T.tVar (rev (seq 0 m))) .: ren (+m)]).[upn m (ren f)]
    = C.[ren (upren f)].[T.tRoll I c (map T.tVar (rev (seq 0 m))) .: ren (+m)].
  Proof.
    rewrite !subst_comp.
    apply (f_equal (fun τ => C.[τ])). extensionality x.
    unfold scomp. destruct x as [|x]; simpl.
    - exact (tRoll_map_tVar_upn_new I c m (ren f)).
    - replace (m + x) with (x + m) by lia.
      rewrite upn_ren_add_new.
      unfold ids, Autosubst_Classes.ids, T.Ids_tm. f_equal. lia.
  Qed.

  Lemma upn_add_new (m : nat) (σ : var -> T.tm) (k : var) :
    upn m σ (k + m) = (σ k).[ren (+m)].
  Proof.
    revert σ k. induction m as [|m IH]; intros σ k.
    - simpl. replace (k + 0) with k by lia. autosubst.
    - replace (k + S m) with (S k + m) by lia.
      change (upn (S m) σ (S k + m)) with ((T.up (upn m σ)) (S k + m)).
      unfold T.up, Autosubst_Classes.up at 1. simpl.
      unfold ids, Autosubst_Classes.ids, T.Ids_tm.
      rewrite IH. rewrite rename_subst, subst_comp.
      apply (f_equal (fun τ => (σ k).[τ])).
      extensionality x. unfold scomp, ren. simpl. reflexivity.
  Qed.

  Lemma branch_body_subst_gen_new (I c m : nat) (C : T.tm) (σ : var -> T.tm) :
    (C.[T.tRoll I c (map T.tVar (rev (seq 0 m))) .: ren (+m)]).[upn m σ]
    = C.[T.up σ].[T.tRoll I c (map T.tVar (rev (seq 0 m))) .: ren (+m)].
  Proof.
    rewrite !subst_comp.
    apply (f_equal (fun τ => C.[τ])). extensionality x.
    unfold scomp. destruct x as [|x]; simpl.
    - exact (tRoll_map_tVar_upn_new I c m σ).
    - replace (m + x) with (x + m) by lia.
      rewrite upn_add_new, rename_subst, subst_comp.
      apply (f_equal (fun τ => (σ x).[τ])).
      extensionality y. unfold scomp, ren. simpl. reflexivity.
  Qed.

  Lemma mk_pis_subst_closed_new (As : list T.tm) (B : T.tm) (σ : var -> T.tm)
      (Hcl : forall n A, In A As -> A.[upn n σ] = A) :
      (mk_pis As B).[σ] = mk_pis As (B.[upn (length As) σ]).
  Proof.
    revert B σ Hcl. induction As as [|A As IH]; intros B σ Hcl.
    - simpl. asimpl. reflexivity.
    - simpl. rewrite IH.
      + f_equal. exact (Hcl 0 A (or_introl eq_refl)). asimpl. reflexivity.
      + intros n A' HA'. rewrite upn_up_eq_new. exact (Hcl (S n) A' (or_intror HA')).
  Qed.

  Lemma list_subst_inv_elem_new (xs : list T.tm) (σ : var -> T.tm) :
    xs..[σ] = xs -> forall A, In A xs -> A.[σ] = A.
  Proof.
    revert xs. intro xs. induction xs as [|x xs IH]; intros Heq A HA.
    - inversion HA.
    - simpl in Heq, HA. injection Heq as Hx Hxs.
      destruct HA as [->|HA]. exact Hx. exact (IH Hxs A HA).
  Qed.

  Lemma As_elem_closed_new (Σenv : env) (I : nat) (ΣI : SP.ind_sig T.tm)
      (c : nat) (ctor : SP.ctor_sig T.tm)
      (Hclosed : closed_param_tys Σenv)
      (HI : SP.lookup_ind Σenv I = Some ΣI)
      (Hc : SP.lookup_ctor ΣI c = Some ctor) :
      let As := SP.ctor_param_tys ctor ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor) in
      forall n A (σ : var -> T.tm), In A As -> A.[upn n σ] = A.
  Proof.
    intros As n A σ HA.
    unfold As in HA. apply in_app_or in HA. destruct HA as [HA|HA].
    - exact (list_subst_inv_elem_new _ _ (Hclosed I ΣI c ctor (upn n σ) HI Hc) A HA).
    - apply repeat_spec in HA. subst A. asimpl. reflexivity.
  Qed.

  Lemma size_in_brs_new (I : nat) (scrut C : T.tm) (brs : list T.tm) (c : nat) (br : T.tm) :
    T.branch brs c = Some br -> T.size br < T.size (T.tCase I scrut C brs).
  Proof.
    intro H. apply nth_error_In in H. simpl.
    induction brs as [|b brs IH]. - inversion H.
    - simpl in H |- *. destruct H as [->|H]. + lia. + specialize (IH H). lia.
  Qed.

  Lemma size_in_args_new (I c : nat) (args : list T.tm) (a : T.tm) :
    In a args -> T.size a < T.size (T.tRoll I c args).
  Proof.
    intro H. simpl.
    induction args as [|b args IH]. - inversion H.
    - simpl in H |- *. destruct H as [->|H]. + lia. + specialize (IH H). lia.
  Qed.

  Lemma firstn_in_list_new (A : Type) (n : nat) (l : list A) (x : A) :
    In x (firstn n l) -> In x l.
  Proof.
    intros H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
  Qed.

  Lemma skipn_in_list_new (A : Type) (n : nat) (l : list A) (x : A) :
    In x (skipn n l) -> In x l.
  Proof.
    intros H. rewrite <- (firstn_skipn n l). apply in_app_iff. right. exact H.
  Qed.

  Lemma split_at_in_params_new (n : nat) (args params recs : list T.tm) :
    split_at n args = (params, recs) ->
    forall p, In p params -> In p args.
  Proof.
    unfold split_at. intro H. injection H as Hp Hr.
    intros p Hin. rewrite <- Hp in Hin. exact (firstn_in_list_new _ _ _ _ Hin).
  Qed.

  Lemma split_at_in_recs_new (n : nat) (args params recs : list T.tm) :
    split_at n args = (params, recs) ->
    forall r, In r recs -> In r args.
  Proof.
    unfold split_at. intro H. injection H as Hp Hr.
    intros r Hin. rewrite <- Hr in Hin. exact (skipn_in_list_new _ _ _ _ Hin).
  Qed.

  Lemma forall2_subst_closed_in_new {Σenv Γ Γ'} {f : var -> var}
      {params tys : list T.tm}
      (H2 : Forall2 (has_type Σenv Γ) params tys)
      (IH : forall p ty, has_type Σenv Γ p ty -> In p params ->
                         has_type Σenv Γ' (p.[ren f]) (ty.[ren f]))
      (Hcl : tys..[ren f] = tys) :
      Forall2 (has_type Σenv Γ') params..[ren f] tys.
  Proof.
    assert (Hstep : Forall2 (has_type Σenv Γ') params..[ren f] tys..[ren f]).
    { clear Hcl. revert IH.
      induction H2 as [|p ty ps ts Hp Hps IHps]; simpl; intros IH.
      - constructor.
      - constructor.
        + apply IH. exact Hp. left. reflexivity.
        + apply IHps. intros p' ty' Hp' Hin'. apply IH. exact Hp'. right. exact Hin'. }
    rewrite Hcl in Hstep. exact Hstep.
  Qed.

  Lemma forall_subst_ind_in_new {Σenv Γ Γ'} {I : nat} {f : var -> var} {recs : list T.tm}
      (H3 : Forall (fun r => has_type Σenv Γ r (T.tInd I [])) recs)
      (IH : forall r, has_type Σenv Γ r (T.tInd I []) -> In r recs ->
                      has_type Σenv Γ' (r.[ren f]) (T.tInd I [])) :
      Forall (fun r => has_type Σenv Γ' r (T.tInd I [])) recs..[ren f].
  Proof.
    revert IH. induction H3 as [|r rs Hr Hrs IHrs]; simpl; intros IH.
    - constructor.
    - constructor.
      + apply IH. exact Hr. left. reflexivity.
      + apply IHrs. intros r' Hr' Hin'. apply IH. exact Hr'. right. exact Hin'.
  Qed.

  Lemma forall2_subst_gen_in_new {Σenv Γ Δ} {σ : var -> T.tm}
      {params tys : list T.tm}
      (H2 : Forall2 (has_type Σenv Γ) params tys)
      (IH : forall p ty, has_type Σenv Γ p ty -> In p params ->
                         has_type Σenv Δ (p.[σ]) (ty.[σ]))
      (Hcl : tys..[σ] = tys) :
      Forall2 (has_type Σenv Δ) params..[σ] tys.
  Proof.
    assert (Hstep : Forall2 (has_type Σenv Δ) params..[σ] tys..[σ]).
    { clear Hcl. revert IH.
      induction H2 as [|p ty ps ts Hp Hps IHps]; simpl; intros IH.
      - constructor.
      - constructor.
        + apply IH. exact Hp. left. reflexivity.
        + apply IHps. intros p' ty' Hp' Hin'. apply IH. exact Hp'. right. exact Hin'. }
    rewrite Hcl in Hstep. exact Hstep.
  Qed.

  Lemma forall_subst_ind_gen_in_new {Σenv Γ Δ} {I : nat} {σ : var -> T.tm} {recs : list T.tm}
      (H3 : Forall (fun r => has_type Σenv Γ r (T.tInd I [])) recs)
      (IH : forall r, has_type Σenv Γ r (T.tInd I []) -> In r recs ->
                      has_type Σenv Δ (r.[σ]) (T.tInd I [])) :
      Forall (fun r => has_type Σenv Δ r (T.tInd I [])) recs..[σ].
  Proof.
    revert IH. induction H3 as [|r rs Hr Hrs IHrs]; simpl; intros IH.
    - constructor.
    - constructor.
      + apply IH. exact Hr. left. reflexivity.
      + apply IHrs. intros r' Hr' Hin'. apply IH. exact Hr'. right. exact Hin'.
  Qed.

  (* ----------------------------------------------------------------
     STEP 1: Renaming substitution (σ = ren f), proved by WF induction.
     ---------------------------------------------------------------- *)

  Definition subst_ren_stmt_new (Σenv : env) (n : nat) : Prop :=
    forall (Γ : ctx) (t A : T.tm) (Hty : has_type Σenv Γ t A),
      T.size t <= n ->
      forall (f : var -> var) (Γ' : ctx)
        (Hf : forall x C, ctx_lookup Γ x = Some C -> ctx_lookup Γ' (f x) = Some C.[ren f]),
      has_type Σenv Γ' (t.[ren f]) (A.[ren f]).

  Lemma subst_ren_step_new (Σenv : env) (Hclosed : closed_param_tys Σenv) :
      forall n, (forall m, m < n -> subst_ren_stmt_new Σenv m) -> subst_ren_stmt_new Σenv n.
  Proof.
    intros n IHn. unfold subst_ren_stmt_new. intros Γ t A Hty Hsize f Γ' Hf.
    destruct Hty; simpl in Hsize |- *.
    - apply ty_var. exact (Hf x A H).
    - apply ty_sort.
    - rewrite up_ren_eq_new. apply ty_pi with (i := i) (j := j).
      + assert (HA : T.size A < n) by (simpl in Hsize; lia).
        exact (IHn _ HA Γ A _ Hty1 (Nat.le_refl _) f Γ' Hf).
      + assert (HB : T.size B < n) by (simpl in Hsize; lia).
        apply (IHn _ HB (A :: Γ) B _ Hty2 (Nat.le_refl _) (upren f) (A.[ren f] :: Γ')).
        apply ctx_lookup_ren_new. exact Hf.
    - rewrite up_ren_eq_new. apply ty_lam with (i := i).
      + assert (HA : T.size A < n) by lia.
        exact (IHn _ HA Γ A _ Hty1 (Nat.le_refl _) f Γ' Hf).
      + assert (Ht : T.size t < n) by lia.
        apply (IHn _ Ht (A :: Γ) t _ Hty2 (Nat.le_refl _) (upren f) (A.[ren f] :: Γ')).
        apply ctx_lookup_ren_new. exact Hf.
    - assert (Ht_fn : T.size t < n) by lia.
      assert (Hu : T.size u < n) by lia.
      pose proof (IHn _ Ht_fn Γ t _ Hty1 (Nat.le_refl _) f Γ' Hf) as IH1.
      simpl in IH1. rewrite up_ren_eq_new in IH1. rewrite subst0_ren_new.
      apply ty_app with (A := A.[ren f]).
      + exact IH1.
      + exact (IHn _ Hu Γ u A Hty2 (Nat.le_refl _) f Γ' Hf).
    - apply ty_fix with (i := i).
      + assert (HA' : T.size A < n) by lia.
        exact (IHn _ HA' Γ A _ Hty1 (Nat.le_refl _) f Γ' Hf).
      + assert (Ht' : T.size t < n) by lia.
        rewrite up_ren_eq_new, shift_ren_upren_new.
        apply (IHn _ Ht' (A :: Γ) t _ Hty2 (Nat.le_refl _) (upren f) (A.[ren f] :: Γ')).
        apply ctx_lookup_ren_new. exact Hf.
    - apply ty_ind. exact H.
    - eapply ty_roll with (param_tys := param_tys).
      + eassumption.
      + eassumption.
      + exact (split_at_subst_new _ _ _ _ _ H1).
      + eassumption.
      + apply (forall2_subst_closed_in_new H3).
        * intros p ty Hp Hpin.
          assert (Hp_in_args : In p args) by
            exact (split_at_in_params_new _ args params recs H1 p Hpin).
          assert (Hp_lt : T.size p < n) by
            exact (Nat.lt_le_trans _ _ _ (size_in_args_new I c args p Hp_in_args) Hsize).
          exact (IHn _ Hp_lt Γ p ty Hp (Nat.le_refl _) f Γ' Hf).
        * rewrite H2. exact (Hclosed I ΣI c ctor (ren f) H H0).
      + apply (forall_subst_ind_in_new H4).
        intros r Hr Hrin.
        assert (Hr_in_args : In r args) by
          exact (split_at_in_recs_new _ args params recs H1 r Hrin).
        assert (Hr_lt : T.size r < n) by
          exact (Nat.lt_le_trans _ _ _ (size_in_args_new I c args r Hr_in_args) Hsize).
        exact (IHn _ Hr_lt Γ r (T.tInd I []) Hr (Nat.le_refl _) f Γ' Hf).
      + rewrite (mmap_length_new (ren f) recs). exact H5.
    - assert (Hscrut : T.size scrut < n) by lia.
      assert (HC : T.size C < n) by lia.
      pose proof (IHn _ Hscrut Γ scrut _ Hty1 (Nat.le_refl _) f Γ' Hf) as IHscrut.
      rewrite subst0_ren_new, up_ren_eq_new.
      apply ty_case with (i := i) (ΣI := ΣI).
      + exact H. + rewrite (mmap_length_new (ren f) brs). exact H0. + exact IHscrut.
      + apply (IHn _ HC (T.tInd I [] :: Γ) C _ Hty2 (Nat.le_refl _)
                   (upren f) (T.tInd I [] :: Γ')).
        apply ctx_lookup_ren_new. exact Hf.
      + intros c ctor0 Hctor. destruct (H1 c ctor0 Hctor) as [br [Hbr Htybr]].
        exists (br.[ren f]). split.
        * exact (branch_subst_new brs c (ren f) br Hbr).
        * pose proof (IHn (T.size br)
            (Nat.lt_le_trans _ _ _ (size_in_brs_new I scrut C brs c br Hbr) Hsize)
            Γ br _ Htybr (Nat.le_refl _) f Γ' Hf) as IHbr.
          simpl in IHbr.
          set (As0 := SP.ctor_param_tys ctor0 ++
                      repeat (T.tInd I []) (SP.ctor_rec_arity ctor0)) in *.
          set (m0 := length As0) in *.
          rewrite (mk_pis_subst_closed_new As0 _ (ren f)
            (fun k A HA => As_elem_closed_new Σenv I ΣI c ctor0 Hclosed H Hctor k A (ren f) HA))
            in IHbr.
          rewrite branch_body_subst_ren_new in IHbr. exact IHbr.
  Qed.

  Lemma has_type_subst_ren (Σenv : env) (Hclosed : closed_param_tys Σenv)
      (Γ : ctx) (t A : T.tm) (Hty : has_type Σenv Γ t A)
      (f : var -> var) (Γ' : ctx)
      (Hf : forall x C, ctx_lookup Γ x = Some C -> ctx_lookup Γ' (f x) = Some C.[ren f]) :
      has_type Σenv Γ' (t.[ren f]) (A.[ren f]).
  Proof.
    exact (well_founded_ind lt_wf (subst_ren_stmt_new Σenv)
      (subst_ren_step_new Σenv Hclosed)
      (T.size t) Γ t A Hty (Nat.le_refl _) f Γ' Hf).
  Qed.

  (* ----------------------------------------------------------------
     STEP 2: has_type_weaken_head (derived from has_type_subst_ren).
     ---------------------------------------------------------------- *)

  Lemma ctx_lookup_S_new (Γ : ctx) (B : T.tm) (x : var) (C : T.tm) :
    ctx_lookup Γ x = Some C -> ctx_lookup (B :: Γ) (S x) = Some C.[ren S].
  Proof.
    intro H. simpl. rewrite H. simpl. rewrite <- shift_eq_ren_S. reflexivity.
  Qed.

  Lemma has_type_weaken_head (Σenv : env) (Γ : ctx) (t A B : T.tm)
      (Hclosed : closed_param_tys Σenv) :
    has_type Σenv Γ t A ->
    has_type Σenv (B :: Γ) (T.shift 1 0 t) (T.shift 1 0 A).
  Proof.
    intro Hty. rewrite !shift_eq_ren_S.
    exact (has_type_subst_ren Σenv Hclosed Γ t A Hty S (B :: Γ) (ctx_lookup_S_new Γ B)).
  Qed.

  (* ----------------------------------------------------------------
     STEP 3: has_type_subst (general σ), proved by WF induction.
     ---------------------------------------------------------------- *)

  Lemma subst0_subst_new (B u : T.tm) (σ : var -> T.tm) :
    (T.subst0 u B).[σ] = T.subst0 (u.[σ]) (B.[T.up σ]).
  Proof.
    unfold T.subst0. rewrite !subst_comp.
    apply (f_equal (fun τ => B.[τ])). extensionality x.
    unfold scomp. destruct x as [|x]; simpl.
    - reflexivity.
    - rewrite rename_subst, subst_comp. asimpl. reflexivity.
  Qed.

  Definition subst_stmt_new (Σenv : env) (Hclosed : closed_param_tys Σenv) (n : nat) : Prop :=
    forall (Γ : ctx) (t A : T.tm) (Hty : has_type Σenv Γ t A),
      T.size t <= n ->
      forall (Δ : ctx) (σ : var -> T.tm)
        (Hσ : forall x, match ctx_lookup Γ x with
                        | Some C => has_type Σenv Δ (σ x) (C.[σ])
                        | None => True
                        end),
      has_type Σenv Δ (t.[σ]) (A.[σ]).

  Lemma subst_step_new (Σenv : env) (Hclosed : closed_param_tys Σenv) :
      forall n, (forall m, m < n -> subst_stmt_new Σenv Hclosed m) ->
                subst_stmt_new Σenv Hclosed n.
  Proof.
    intros n IHn. unfold subst_stmt_new. intros Γ t A Hty Hsize Δ σ Hσ.
    assert (Hup : forall E,
      forall x, match ctx_lookup (E :: Γ) x with
                | Some C => has_type Σenv (E.[σ] :: Δ) (T.up σ x) (C.[T.up σ])
                | None => True
                end).
    { intros E [|x]; simpl.
      - rewrite shift_up_eq_new. unfold T.up, Autosubst_Classes.up. simpl.
        apply ty_var. simpl. reflexivity.
      - specialize (Hσ x). destruct (ctx_lookup Γ x) as [C|] eqn:HC; simpl.
        + rewrite shift_up_eq_new.
          unfold T.up, Autosubst_Classes.up at 1. simpl. rewrite rename_subst.
          rewrite <- shift_eq_ren_S.
          exact (has_type_weaken_head Σenv Δ (σ x) (C.[σ]) (E.[σ]) Hclosed Hσ).
        + exact I. }
    destruct Hty; simpl in Hsize |- *.
    - specialize (Hσ x). rewrite H in Hσ. exact Hσ.
    - apply ty_sort.
    - apply ty_pi with (i := i) (j := j).
      + assert (HA_lt : T.size A < n) by lia.
        exact (IHn _ HA_lt Γ A _ Hty1 (Nat.le_refl _) Δ σ Hσ).
      + assert (HB_lt : T.size B < n) by lia.
        apply (IHn _ HB_lt (A :: Γ) B _ Hty2 (Nat.le_refl _) (A.[σ] :: Δ) (T.up σ) (Hup A)).
    - apply ty_lam with (i := i).
      + assert (HA_lt2 : T.size A < n) by lia.
        exact (IHn _ HA_lt2 Γ A _ Hty1 (Nat.le_refl _) Δ σ Hσ).
      + assert (Ht_lt2 : T.size t < n) by lia.
        apply (IHn _ Ht_lt2 (A :: Γ) t _ Hty2 (Nat.le_refl _) (A.[σ] :: Δ) (T.up σ) (Hup A)).
    - assert (Ht_fn : T.size t < n) by lia.
      assert (Hu : T.size u < n) by lia.
      pose proof (IHn _ Ht_fn Γ t _ Hty1 (Nat.le_refl _) Δ σ Hσ) as IH1.
      simpl in IH1. rewrite subst0_subst_new.
      apply ty_app with (A := A.[σ]).
      + exact IH1.
      + exact (IHn _ Hu Γ u A Hty2 (Nat.le_refl _) Δ σ Hσ).
    - apply ty_fix with (i := i).
      + assert (HA_lt3 : T.size A < n) by lia.
        exact (IHn _ HA_lt3 Γ A _ Hty1 (Nat.le_refl _) Δ σ Hσ).
      + assert (Ht_lt3 : T.size t < n) by lia.
        rewrite <- shift_up_eq_new.
        apply (IHn _ Ht_lt3 (A :: Γ) t _ Hty2 (Nat.le_refl _) (A.[σ] :: Δ) (T.up σ) (Hup A)).
    - apply ty_ind. exact H.
     - eapply ty_roll with (param_tys := param_tys).
       + eassumption.
       + eassumption.
       + exact (split_at_subst_new _ _ _ _ _ H1).
       + eassumption.
       + apply (forall2_subst_gen_in_new H3).
        * intros p ty Hp Hpin.
          assert (Hp_in_args : In p args) by
            exact (split_at_in_params_new _ args params recs H1 p Hpin).
          assert (Hp_lt : T.size p < n) by
            exact (Nat.lt_le_trans _ _ _ (size_in_args_new I c args p Hp_in_args) Hsize).
          exact (IHn _ Hp_lt Γ p ty Hp (Nat.le_refl _) Δ σ Hσ).
        * rewrite H2. exact (Hclosed I ΣI c ctor σ H H0).
      + apply (forall_subst_ind_gen_in_new H4).
        intros r Hr Hrin.
        assert (Hr_in_args : In r args) by
          exact (split_at_in_recs_new _ args params recs H1 r Hrin).
        assert (Hr_lt : T.size r < n) by
          exact (Nat.lt_le_trans _ _ _ (size_in_args_new I c args r Hr_in_args) Hsize).
        exact (IHn _ Hr_lt Γ r (T.tInd I []) Hr (Nat.le_refl _) Δ σ Hσ).
      + rewrite (mmap_length_new σ recs). exact H5.
    - assert (Hscrut : T.size scrut < n) by lia.
      assert (HC : T.size C < n) by lia.
      pose proof (IHn _ Hscrut Γ scrut _ Hty1 (Nat.le_refl _) Δ σ Hσ) as IHscrut.
      rewrite subst0_subst_new.
      apply ty_case with (i := i) (ΣI := ΣI).
      + exact H. + rewrite (mmap_length_new σ brs). exact H0. + exact IHscrut.
      + apply (IHn _ HC (T.tInd I [] :: Γ) C _ Hty2 (Nat.le_refl _)
                   (T.tInd I [] :: Δ) (T.up σ) (Hup (T.tInd I []))).
      + intros c ctor0 Hctor. destruct (H1 c ctor0 Hctor) as [br [Hbr Htybr]].
        exists (br.[σ]). split.
        * exact (branch_subst_new brs c σ br Hbr).
        * assert (Hbr_lt : T.size br < n) by
            exact (Nat.lt_le_trans _ _ _ (size_in_brs_new I scrut C brs c br Hbr) Hsize).
          pose proof (IHn _ Hbr_lt Γ br _ Htybr (Nat.le_refl _) Δ σ Hσ) as IHbr.
          simpl in IHbr.
          pose proof (mk_pis_subst_closed_new
            (SP.ctor_param_tys ctor0 ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor0))
            (C.[T.tRoll I c (map T.tVar (rev (seq 0 (length
              (SP.ctor_param_tys ctor0 ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor0)))))) .:
              ren (+length (SP.ctor_param_tys ctor0 ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor0)))])
            σ
            (fun k A HA => As_elem_closed_new Σenv I ΣI c ctor0 Hclosed H Hctor k A σ HA)) as Heqmk.
          rewrite Heqmk in IHbr.
          pose proof (branch_body_subst_gen_new I c
            (length (SP.ctor_param_tys ctor0 ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor0)))
            C σ) as Heqbr.
          rewrite Heqbr in IHbr.
          exact IHbr.
  Qed.

  Lemma has_type_subst (Σenv : env) (Γ Δ : ctx) (σ : var -> T.tm) (t A : T.tm)
      (Hclosed : closed_param_tys Σenv) :
    has_type Σenv Γ t A ->
    (forall x, match ctx_lookup Γ x with
      | Some C => has_type Σenv Δ (σ x) (C.[σ])
      | None => True
      end) ->
    has_type Σenv Δ (t.[σ]) (A.[σ]).
  Proof.
    intros Hty Hσ.
    exact (well_founded_ind lt_wf (subst_stmt_new Σenv Hclosed)
      (subst_step_new Σenv Hclosed)
      (T.size t) Γ t A Hty (Nat.le_refl _) Δ σ Hσ).
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
