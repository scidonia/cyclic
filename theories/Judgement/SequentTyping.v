From Stdlib Require Import List Arith Lia Utf8.
From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.

Import ListNotations.

Set Default Proof Using "Type".

Module SequentTyping.
  Module T := Term.Syntax.
  Module Ty := Typing.Typing.
  Module SP := StrictPos.

  (** Bidirectional sequent-style typing (term-level).

      This is a lightweight "sequent" presentation in the sense that we split the
      typing judgement into:

      - [syn Σ Γ t A] : t synthesizes type A
      - [chk Σ Γ t A] : t checks against type A

      This is intentionally *not* a normalized/definitional-equality driven
      system: we only use the syntactic type constructors already present in the
      term, and we provide a minimal subsumption rule [chk_of_syn].

      The purpose of this file is to give a Curry--Howard style "write-down" of
      a term as a sequent proof tree that we can later turn into a graph and then
      normalize by sequent transformations (supercompilation).
   *)

  Inductive syn (Σenv : Ty.env) : Ty.ctx -> T.tm -> T.tm -> Prop :=
  | syn_var Γ x A :
      Ty.ctx_lookup Γ x = Some A ->
      syn Σenv Γ (T.tVar x) A

  | syn_sort Γ i :
      syn Σenv Γ (T.tSort i) (T.tSort (S i))

  | syn_pi Γ A B i j :
      chk Σenv Γ A (T.tSort i) ->
      chk Σenv (Ty.ctx_extend Γ A) B (T.tSort j) ->
      syn Σenv Γ (T.tPi A B) (T.tSort (Nat.max i j))

  | syn_lam Γ A t B i :
      chk Σenv Γ A (T.tSort i) ->
      chk Σenv (Ty.ctx_extend Γ A) t B ->
      syn Σenv Γ (T.tLam A t) (T.tPi A B)

  | syn_app Γ t u A B :
      syn Σenv Γ t (T.tPi A B) ->
      chk Σenv Γ u A ->
      syn Σenv Γ (T.tApp t u) (T.subst0 u B)

  | syn_fix Γ A t i :
      chk Σenv Γ A (T.tSort i) ->
      chk Σenv (Ty.ctx_extend Γ A) t (T.shift 1 0 A) ->
      syn Σenv Γ (T.tFix A t) A

  | syn_ind_tm Γ I ΣI :
      SP.lookup_ind Σenv I = Some ΣI ->
      syn Σenv Γ (T.tInd I []) (T.tSort (S (SP.ind_level ΣI)))

  | syn_roll Γ I ΣI c ctor args params recs :
      SP.lookup_ind Σenv I = Some ΣI ->
      SP.lookup_ctor ΣI c = Some ctor ->
      Ty.split_at (SP.ctor_param_arity ctor) args = (params, recs) ->
      Forall2 (chk Σenv Γ) params (SP.ctor_param_tys ctor) ->
      Forall (fun r => chk Σenv Γ r (T.tInd I [])) recs ->
      length recs = SP.ctor_rec_arity ctor ->
      syn Σenv Γ (T.tRoll I c args) (T.tInd I [])

  | syn_case Γ I ΣI scrut C brs i :
      SP.lookup_ind Σenv I = Some ΣI ->
      length brs = length (SP.ind_ctors ΣI) ->
      chk Σenv Γ scrut (T.tInd I []) ->
      chk Σenv (Ty.ctx_extend Γ (T.tInd I [])) C (T.tSort i) ->
      (forall c ctor,
        SP.lookup_ctor ΣI c = Some ctor ->
        exists br,
          T.branch brs c = Some br
          /\
          let As := SP.ctor_param_tys ctor ++ repeat (T.tInd I []) (SP.ctor_rec_arity ctor) in
          let m := length As in
          chk Σenv Γ br
            (Ty.mk_pis As (C.[T.tRoll I c (map T.tVar (rev (seq 0 m))) .: ren (+m)]))) ->
      syn Σenv Γ (T.tCase I scrut C brs) (T.subst0 scrut C)

  with chk (Σenv : Ty.env) : Ty.ctx -> T.tm -> T.tm -> Prop :=
  | chk_of_syn Γ t A :
      syn Σenv Γ t A ->
      chk Σenv Γ t A.

  (** Curry--Howard write-down: every [Typing.has_type] derivation can be seen as
      a sequent proof in this bidirectional system.

      This is the intended "starting point": it is not normalized; it just
      re-expresses the existing typing derivation in a sequent/bidirectional
      shape.
   *)

  Lemma has_type_to_syn (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
    Ty.has_type Σenv Γ t A -> syn Σenv Γ t A.
  Proof.
    revert Γ t A.
    refine (fix F (Γ : Ty.ctx) (t A : T.tm) (Hty : Ty.has_type Σenv Γ t A) {struct Hty}
            : syn Σenv Γ t A := _).
    destruct Hty.
    - (* var *)
      econstructor. exact H.
    - (* sort *)
      constructor.
    - (* pi *)
      eapply syn_pi.
      + apply chk_of_syn. exact (F _ _ _ Hty1).
      + apply chk_of_syn. exact (F _ _ _ Hty2).
    - (* lam *)
      eapply syn_lam.
      + apply chk_of_syn. exact (F _ _ _ Hty1).
      + apply chk_of_syn. exact (F _ _ _ Hty2).
    - (* app *)
      eapply syn_app.
      + exact (F _ _ _ Hty1).
      + apply chk_of_syn. exact (F _ _ _ Hty2).
    - (* fix *)
      eapply syn_fix.
      + apply chk_of_syn. exact (F _ _ _ Hty1).
      + apply chk_of_syn. exact (F _ _ _ Hty2).
    - (* ind *)
      eapply syn_ind_tm; eauto.
    - (* roll *)
      eapply syn_roll; try eassumption.
      + clear -F H2.
        induction H2 as [|t A ts As Ht Hts IH]; constructor.
        * apply chk_of_syn. exact (F _ _ _ Ht).
        * exact IH.
      + clear -F H3.
        induction H3 as [|r rs Hr Hrs IH]; constructor.
        * apply chk_of_syn. exact (F _ _ _ Hr).
        * exact IH.
    - (* case *)
      eapply syn_case; try eassumption.
      + apply chk_of_syn. exact (F _ _ _ Hty1).
      + apply chk_of_syn. exact (F _ _ _ Hty2).
      + intros c ctor Hctor.
        destruct (H1 c ctor Hctor) as [br [Hbr Htybr]].
        exists br. split; [exact Hbr|].
        apply chk_of_syn.
        exact (F _ _ _ Htybr).
  Qed.

  Lemma has_type_to_chk (Σenv : Ty.env) (Γ : Ty.ctx) (t A : T.tm) :
    Ty.has_type Σenv Γ t A -> chk Σenv Γ t A.
  Proof.
    intro Hty.
    apply chk_of_syn.
    exact (has_type_to_syn Σenv Γ t A Hty).
  Qed.

End SequentTyping.
