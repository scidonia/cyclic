From Stdlib Require Import List Bool Arith Utf8.
From stdpp Require Import gmap.

From Autosubst Require Import Autosubst.

From Cyclic.Syntax Require Import StrictPos Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Semantics Require Import Cbn.
From Cyclic.Transform Require Import BetaReduce CaseCase.
From Cyclic.Progress Require Import PatternUnification.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module PU := PatternUnification.
Module CC := CaseCase.

Definition config : Type := C.judgement.

Definition tm_eqb : tm -> tm -> bool := PU.tm_eqb.

Definition ctx_eqb (Γ Δ : Ty.ctx) : bool :=
  PU.list_eqb tm_eqb Γ Δ.

Definition sub_eqb (s1 s2 : Ty.sub) : bool :=
  Nat.eqb (Ty.sub_k s1) (Ty.sub_k s2)
  && PU.list_eqb tm_eqb (Ty.sub_list s1) (Ty.sub_list s2).

Definition judgement_eqb (j1 j2 : config) : bool :=
  match j1, j2 with
  | C.jTy Γ t A, C.jTy Γ' t' A' =>
      ctx_eqb Γ Γ' && tm_eqb t t' && tm_eqb A A'
  | C.jEq Γ t u A, C.jEq Γ' t' u' A' =>
      ctx_eqb Γ Γ' && tm_eqb t t' && tm_eqb u u' && tm_eqb A A'
  | C.jSub Δ s Γ, C.jSub Δ' s' Γ' =>
      ctx_eqb Δ Δ' && sub_eqb s s' && ctx_eqb Γ Γ'
  | _, _ => false
  end.

Lemma ctx_eqb_eq : forall Γ Δ,
  ctx_eqb Γ Δ = true -> Γ = Δ.
Proof.
  intros Γ Δ H.
  unfold ctx_eqb in H.
  eapply (PU.list_eqb_eq tm_eqb).
  - intros x y. apply PU.tm_eqb_eq.
  - exact H.
Qed.

Lemma sub_eqb_eq : forall s1 s2,
  sub_eqb s1 s2 = true -> s1 = s2.
Proof. Admitted.

Lemma judgement_eqb_eq : forall j1 j2,
  judgement_eqb j1 j2 = true -> j1 = j2.
Proof. Admitted.

Fixpoint memo_lookup (j : config) (memo : list (config * nat)) : option nat :=
  match memo with
  | [] => None
  | (j', v) :: memo => if judgement_eqb j j' then Some v else memo_lookup j memo
  end.

Fixpoint nub_tm (xs : list tm) : list tm :=
  match xs with
  | [] => []
  | x :: xs =>
      let ys := nub_tm xs in
      if existsb (fun y => tm_eqb x y) ys then ys else x :: ys
  end.

Definition rewrite_step : Type := tm -> tm.

(** * Proper CBN driving (β/iota/fix + scrutinee driving)

    This is the operational "driving" component that enables deforestation and
    fusion: we unfold and reduce according to the call-by-name semantics from
    `Semantics/Cbn.v`.

    Important: this is *not* a domain-specific rewrite (no `length∘map` axiom).
    Any fusion we get must emerge from unfolding + case commuting + folding.
*)

Fixpoint drive_cbn_once (t : tm) : tm :=
  match t with
  | tApp t1 t2 =>
      let t1' := drive_cbn_once t1 in
      match t1' with
      | tLam A body => subst0 t2 body
      | _ => tApp t1' t2
      end
  | tFix A body => subst0 (tFix A body) body
  | tCase ind scrut C brs =>
      match scrut with
      | tRoll ind' c args =>
          if Nat.eqb ind ind' then
            match branch brs c with
            | Some br => Cbn.apps br args
            | None => t
            end
          else t
      | _ =>
          let scrut' := drive_cbn_once scrut in
          if tm_eqb scrut scrut' then t else tCase ind scrut' C brs
      end
  | _ => t
  end.

Fixpoint whnf_drive (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t' := drive_cbn_once t in
      if tm_eqb t t' then t else whnf_drive fuel' t'
  end.

Fixpoint supercompile_tm (fuel : nat) (Σenv : Ty.env) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t1 := whnf_drive fuel' t in
      let t2 := CC.commute_case_case_once_typed Σenv t1 in
      let t3 := CC.propagate_motive_once t2 in
      (* drive under binders / subterms *)
      match t3 with
      | tLam A body =>
          tLam (supercompile_tm fuel' Σenv A) (supercompile_tm fuel' Σenv body)
      | tPi A B =>
          tPi (supercompile_tm fuel' Σenv A) (supercompile_tm fuel' Σenv B)
      | tApp t4 t5 =>
          (* after driving the head, only descend structurally *)
          tApp (supercompile_tm fuel' Σenv t4) (supercompile_tm fuel' Σenv t5)
      | tFix A body =>
          tFix (supercompile_tm fuel' Σenv A) (supercompile_tm fuel' Σenv body)
      | tInd ind args =>
          tInd ind (map (supercompile_tm fuel' Σenv) args)
      | tRoll ind c args =>
          tRoll ind c (map (supercompile_tm fuel' Σenv) args)
      | tCase ind scrut C brs =>
          tCase ind
            (supercompile_tm fuel' Σenv scrut)
            (supercompile_tm fuel' Σenv C)
            (map (supercompile_tm fuel' Σenv) brs)
      | _ => t3
      end
  end.

Definition drive_terms (rewrites : list rewrite_step) (t : tm) : list tm :=
  nub_tm (filter (fun u => negb (tm_eqb t u)) (map (fun f => f t) rewrites)).

(** Full normalization: drive under binders.
    This recursively applies transformations to subterms,
    including those under lambda, pi, fix, and case motives. *)
Fixpoint drive_under_binders (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t' :=
        match t with
        | tLam A body =>
            tLam (drive_under_binders fuel' A) (drive_under_binders fuel' body)
        | tPi A B =>
            tPi (drive_under_binders fuel' A) (drive_under_binders fuel' B)
        | tApp t1 t2 =>
            (* First try head reduction *)
            let t_head := BetaReduce.beta_reduce_once t in
            if negb (tm_eqb t t_head) then
              drive_under_binders fuel' t_head
            else
              tApp (drive_under_binders fuel' t1) (drive_under_binders fuel' t2)
        | tFix A body =>
            tFix (drive_under_binders fuel' A) (drive_under_binders fuel' body)
        | tCase ind scrut C brs =>
            (* Try case-of-constructor reduction first *)
            let scrut' := drive_under_binders fuel' scrut in
            tCase ind scrut'
                  (drive_under_binders fuel' C)
                  (map (drive_under_binders fuel') brs)
        | tRoll ind c args =>
            tRoll ind c (map (drive_under_binders fuel') args)
        | tInd ind args =>
            tInd ind (map (drive_under_binders fuel') args)
        | _ => t
        end
      in t'
  end.

Definition commute_case_case_in_scrut (Σenv : Ty.env) (t : tm) : tm :=
  match t with
  | tCase ind scrut C brs =>
      let scrut' := CC.commute_case_case_once_typed Σenv scrut in
      if tm_eqb scrut scrut' then t else tCase ind scrut' C brs
  | _ => t
  end.

Definition memo_norm_fuel : nat := 30.
Definition drive_norm_fuel : nat := 10.

Definition default_rewrites (Σenv : Ty.env) : list rewrite_step :=
  [drive_cbn_once;
   (fun t => whnf_drive 20 t);
   CC.commute_case_case_once_typed Σenv;
   commute_case_case_in_scrut Σenv;
   CC.propagate_motive_once].

(** Small normalisation pipeline used for memo/whistle.

    This is intentionally bounded and deterministic: it just iterates the
    generic driving + case-case commuting conversions to a fixed point.
*)
Fixpoint commute_case_case_nf (fuel : nat) (Σenv : Ty.env) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t' := CC.commute_case_case_once_typed Σenv t in
      if tm_eqb t t' then t else commute_case_case_nf fuel' Σenv t'
  end.

Fixpoint propagate_motive_nf (fuel : nat) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t' := CC.propagate_motive_once t in
      if tm_eqb t t' then t else propagate_motive_nf fuel' t'
  end.

Fixpoint norm_tm (fuel : nat) (Σenv : Ty.env) (t : tm) : tm :=
  match fuel with
  | 0 => t
  | S fuel' =>
      let t1 := whnf_drive 50 t in
      let t2 := commute_case_case_nf 50 Σenv t1 in
      let t3 := propagate_motive_nf 20 t2 in
      if tm_eqb t t3 then t3 else norm_tm fuel' Σenv t3
  end.

Definition norm_config (fuel : nat) (Σenv : Ty.env) (j : config) : config :=
  match j with
  | C.jTy Γ t A => C.jTy Γ (norm_tm fuel Σenv t) (norm_tm fuel Σenv A)
  | _ => j
  end.

(** * Configuration canonicalisation (context trimming)

    Case-splitting introduces fresh variables for constructor arguments.
    Without trimming, contexts monotonically grow along recursive calls and exact
    memoisation never fires. We therefore "garbage collect" unused variables:

    - compute free variables of the term/type
    - restrict the context to those variables
    - rename term/type/context accordingly

    This is a standard supercompilation administrative step and is not a
    domain-specific rewrite.
*)

Fixpoint nub_nat (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs =>
      let ys := nub_nat xs in
      if existsb (Nat.eqb x) ys then ys else x :: ys
  end.

Fixpoint fv_under_binder (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs =>
      match x with
      | 0 => fv_under_binder xs
      | S x => x :: fv_under_binder xs
      end
  end.

Fixpoint fv_tm (t : tm) : list nat :=
  match t with
  | tVar x => [x]
  | tSort _ => []
  | tPi A B => fv_tm A ++ fv_under_binder (fv_tm B)
  | tLam A body => fv_tm A ++ fv_under_binder (fv_tm body)
  | tApp t1 t2 => fv_tm t1 ++ fv_tm t2
  | tFix A body => fv_tm A ++ fv_under_binder (fv_tm body)
  | tInd _ args => concat (map fv_tm args)
  | tRoll _ _ args => concat (map fv_tm args)
  | tCase _ scrut C brs => fv_tm scrut ++ fv_under_binder (fv_tm C) ++ concat (map fv_tm brs)
  end.

Fixpoint index_of (x : nat) (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | y :: ys =>
      if Nat.eqb x y then Some 0 else option_map S (index_of x ys)
  end.

Fixpoint insert_nat (x : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => [x]
  | y :: ys => if Nat.leb x y then x :: xs else y :: insert_nat x ys
  end.

Fixpoint sort_nat (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs => insert_nat x (sort_nat xs)
  end.

Definition canon_jTy (Γ : Ty.ctx) (t A : tm) : config :=
  let keep := sort_nat (nub_nat (fv_tm t ++ fv_tm A)) in
  let renfun := fun x => default 0 (index_of x keep) in
  let pick_ty :=
        fun x =>
          match nth_error Γ x with
          | Some B => rename renfun B
          | None => tVar 0
          end
  in
  let Γ' := map pick_ty keep in
  C.jTy Γ' (rename renfun t) (rename renfun A).

Definition canon_config (j : config) : config :=
  match j with
  | C.jTy Γ t A => canon_jTy Γ t A
  | _ => j
  end.

Definition fresh_args (n : nat) : list tm :=
  rev (map tVar (seq 0 n)).

Definition subst_one (k : nat) (u : tm) :=
  fun x => if Nat.eqb x k then u else tVar x.

Definition extend_ctx (tys : list tm) (Γ : Ty.ctx) : Ty.ctx :=
  rev tys ++ Γ.

(** Case-splitting / information propagation.

    If driving exposes a neutral case-scrutinee, we split into one successor per
    constructor of the scrutinee inductive, introducing fresh variables for the
    constructor arguments and substituting the scrutinee variable with a `roll`
    built from those variables.
*)
Definition split_case_var
    (Σenv : Ty.env) (Γ : Ty.ctx) (ind : nat) (x : nat)
    (Cmot : tm) (brs : list tm) (A : tm) : list config :=
  match SP.lookup_ind Σenv ind with
  | None => []
  | Some ΣI =>
      let nctors := length (SP.ind_ctors ΣI) in
      let cs := seq 0 nctors in
      concat
        (map
           (fun c =>
              match CC.ctor_arg_tys Σenv ind c with
              | None => []
              | Some tys =>
                  let n := length tys in
                  let Γ' := extend_ctx tys Γ in
                  let args := fresh_args n in
                  let scrut := tRoll ind c args in
                  let σ := subst_one (x + n) scrut in
                  (* shift the whole judgement into the extended context *)
                  let t0 := shift n 0 (tCase ind (tVar x) Cmot brs) in
                  let A0 := shift n 0 A in
                  (* propagate the constructor fact by substitution *)
                  let t1 := t0.[σ] in
                  let A1 := A0.[σ] in
                  (* immediately drive once to perform the iota-step *)
                  let t2 := whnf_drive 5 t1 in
                  [C.jTy Γ' t2 A1]
              end)
           cs)
  end.

Definition drive_step (Σenv : Ty.env) (j : config) : list config :=
  let j := canon_config (norm_config drive_norm_fuel Σenv j) in
  match j with
  | C.jTy Γ t A =>
      let t1 := norm_tm drive_norm_fuel Σenv t in
      (* Observation-driven driving for Nat: keep going under succ thunks.

         This is needed because in the operational semantics `tRoll` is a value
         regardless of its arguments, so WHNF driving would stop too early to
         discover fusion for programs returning Nat.
      *)
      match A, t1 with
      | tInd 0 [], tRoll 0 0 [] => []
      | tInd 0 [], tRoll 0 1 [t'] => [canon_config (norm_config 6 Σenv (C.jTy Γ t' A))]
      | _, _ =>
          match t1 with
          | tCase ind (tVar x) Cmot brs =>
              let splits := split_case_var Σenv Γ ind x Cmot brs A in
          match splits with
          | [] =>
              let ds := drive_terms (default_rewrites Σenv) t1 in
              match ds with
              | [] =>
                  (* If we're stuck on a nested scrutinee case, try commuting
                     inside the scrutinee once to expose a split. *)
                  match t1 with
                  | tCase ind scrut Cmot brs =>
                      let scrut' := CC.commute_case_case_once_typed Σenv scrut in
                      if tm_eqb scrut scrut' then []
                      else [canon_config (C.jTy Γ (tCase ind scrut' Cmot brs) A)]
                  | _ => []
                  end
              | _ => map (fun u => canon_config (C.jTy Γ u A)) ds
              end
          | _ => map canon_config splits
          end
      | _ =>
          let ds := drive_terms (default_rewrites Σenv) t1 in
          match ds with
          | [] =>
              match t1 with
              | tCase ind scrut Cmot brs =>
                  let scrut' := CC.commute_case_case_once_typed Σenv scrut in
                  if tm_eqb scrut scrut' then []
                  else [canon_config (C.jTy Γ (tCase ind scrut' Cmot brs) A)]
              | _ => []
              end
          | _ => map (fun u => canon_config (C.jTy Γ u A)) ds
          end
      end
      end
  | _ => []
  end.

(* A computable approximation of the embedding/whistle relation.
   The Prop-level relation lives in `theories/Progress/Embedding.v`.
   For now we use a fuelled boolean check with the same intended shape:
   the *first* argument is the potentially larger term/judgement. *)

Fixpoint emb_list_b (fuel : nat) (embA : tm -> tm -> bool) (xs ys : list tm) : bool :=
  match fuel with
  | 0 =>
      match ys with
      | [] => true
      | _ => false
      end
  | S fuel' =>
      match xs, ys with
      | _, [] => true
      | [], _ :: _ => false
      | x :: xs', y :: ys' =>
          (* couple or skip *)
          (embA x y && emb_list_b fuel' embA xs' ys')
          || emb_list_b fuel' embA xs' ys
      end
  end.

Fixpoint emb_tm_b (fuel : nat) (t u : tm) : bool :=
  match fuel with
  | 0 => tm_eqb t u
  | S fuel' =>
      if tm_eqb t u then true
      else
        (* diving first *)
        let dive :=
          match t with
          | tPi A B => emb_tm_b fuel' A u || emb_tm_b fuel' B u
          | tLam A body => emb_tm_b fuel' A u || emb_tm_b fuel' body u
          | tApp t1 t2 => emb_tm_b fuel' t1 u || emb_tm_b fuel' t2 u
          | tFix A body => emb_tm_b fuel' A u || emb_tm_b fuel' body u
          | tInd _ args => existsb (fun a => emb_tm_b fuel' a u) args
          | tRoll _ _ args => existsb (fun a => emb_tm_b fuel' a u) args
          | tCase _ scrut C0 brs =>
              emb_tm_b fuel' scrut u
              || emb_tm_b fuel' C0 u
              || existsb (fun br => emb_tm_b fuel' br u) brs
          | _ => false
          end
        in
        if dive then true
        else
          (* coupling *)
          match t, u with
          | tSort i, tSort j => Nat.eqb i j
          | tVar x, tVar y => Nat.eqb x y
          | tInd ind args, tInd ind' args' =>
              Nat.eqb ind ind' && emb_list_b fuel' (emb_tm_b fuel') args args'
          | tPi A B, tPi A' B' => emb_tm_b fuel' A A' && emb_tm_b fuel' B B'
          | tLam A body, tLam A' body' => emb_tm_b fuel' A A' && emb_tm_b fuel' body body'
          | tApp t1 t2, tApp u1 u2 => emb_tm_b fuel' t1 u1 && emb_tm_b fuel' t2 u2
          | tFix A body, tFix A' body' => emb_tm_b fuel' A A' && emb_tm_b fuel' body body'
          | tRoll ind c args, tRoll ind' c' args' =>
              Nat.eqb ind ind' && Nat.eqb c c' && emb_list_b fuel' (emb_tm_b fuel') args args'
          | tCase ind scrut C0 brs, tCase ind' scrut' C0' brs' =>
              Nat.eqb ind ind'
              && emb_tm_b fuel' scrut scrut'
              && emb_tm_b fuel' C0 C0'
              && emb_list_b fuel' (emb_tm_b fuel') brs brs'
          | _, _ => false
          end
  end.

Definition emb_ctx_b (fuel : nat) (Γ Δ : Ty.ctx) : bool :=
  emb_list_b fuel (emb_tm_b fuel) Γ Δ.

Definition emb_sub_b (fuel : nat) (s1 s2 : Ty.sub) : bool :=
  Nat.eqb (Ty.sub_k s1) (Ty.sub_k s2)
  && emb_list_b fuel (emb_tm_b fuel) (Ty.sub_list s1) (Ty.sub_list s2).

Definition emb_judgement_b (fuel : nat) (j1 j2 : config) : bool :=
  match j1, j2 with
  | C.jTy Γ t A, C.jTy Δ u B =>
      emb_ctx_b fuel Γ Δ && emb_tm_b fuel t u && emb_tm_b fuel A B
  | C.jEq Γ t u A, C.jEq Δ t' u' B =>
      emb_ctx_b fuel Γ Δ
      && emb_tm_b fuel t t'
      && emb_tm_b fuel u u'
      && emb_tm_b fuel A B
  | C.jSub Δ s Γ, C.jSub Δ' s' Γ' =>
      emb_ctx_b fuel Δ Δ' && emb_sub_b fuel s s' && emb_ctx_b fuel Γ Γ'
  | _, _ => false
  end.

Fixpoint whistle_candidates (fuel : nat) (j : config) (memo : list (config * nat)) : list (config * nat) :=
  match memo with
  | [] => []
  | (j_prev, v_prev) :: memo =>
      if emb_judgement_b fuel j j_prev
      then (j_prev, v_prev) :: whistle_candidates fuel j memo
      else whistle_candidates fuel j memo
  end.

Definition dominates (fuel : nat) (a b : config) : bool :=
  emb_judgement_b fuel a b && negb (emb_judgement_b fuel b a).

Fixpoint has_dominator (fuel : nat) (j : config) (cands : list (config * nat)) : bool :=
  match cands with
  | [] => false
  | (k, _) :: cs => if dominates fuel k j then true else has_dominator fuel j cs
  end.

Definition maximal_candidates (fuel : nat) (cands : list (config * nat)) : list (config * nat) :=
  filter (fun '(j, _) => negb (has_dominator fuel j cands)) cands.


(* Generalisation wrapper: we reuse the existing computational anti-unifier.
   This is deliberately lightweight (typedness proofs can follow later). *)

Record gen_result : Type := {
  gen_holes : list tm;
  gen_j : config;
  gen_sub1 : list tm;
  gen_sub2 : list tm;
}.

Definition is_trivial_generalisation (r : PU.au_judgement_result) : bool :=
  match PU.auJ_gen r with
  | C.jTy _Γ t _A =>
      match PU.auJ_holes r, t with
      | [_], tVar 0 => true
      | _, _ => false
      end
  | _ => false
  end.

Definition generalize_raw (j1 j2 : config) : option gen_result :=
  match PU.anti_unify_judgement j1 j2 with
  | None => None
  | Some r =>
      Some
        {| gen_holes := PU.auJ_holes r;
           gen_j := PU.auJ_gen r;
           gen_sub1 := PU.auJ_sub1 r;
           gen_sub2 := PU.auJ_sub2 r |}
  end.

Definition generalize_nontrivial (j1 j2 : config) : option gen_result :=
  match PU.anti_unify_judgement j1 j2 with
  | None => None
  | Some r =>
      (* If AU collapses the whole term to one hole, it is usually not helpful
         for deforestation/fusion. *)
      if is_trivial_generalisation r then None else
        Some
          {| gen_holes := PU.auJ_holes r;
             gen_j := PU.auJ_gen r;
             gen_sub1 := PU.auJ_sub1 r;
             gen_sub2 := PU.auJ_sub2 r |}
  end.

Definition gen_term_shape_score (j : config) : nat :=
  match j with
  | C.jTy _Γ t _A =>
      match t with
      | tCase _ _ _ _ => 0
      | tRoll _ _ _ => 1
      | tApp _ _ => 2
      | tLam _ _ => 3
      | _ => 4
      end
  | _ => 10
  end.

Definition gen_score (g : gen_result) : nat * nat :=
  (length g.(gen_holes), gen_term_shape_score g.(gen_j)).

Definition gen_score_le (s1 s2 : nat * nat) : bool :=
  match s1, s2 with
  | (h1, k1), (h2, k2) => Nat.leb h1 h2 && Nat.leb k1 k2
  end.

Fixpoint best_generalize_with
    (gen : config -> config -> option gen_result)
    (j : config) (cands : list (config * nat)) : option (gen_result * nat) :=
  match cands with
  | [] => None
  | (j_prev, v_prev) :: cs =>
      match gen j_prev j with
      | None => best_generalize_with gen j cs
      | Some g =>
          match best_generalize_with gen j cs with
          | None => Some (g, v_prev)
          | Some (g', v') =>
              if gen_score_le (gen_score g) (gen_score g')
              then Some (g, v_prev)
              else Some (g', v')
          end
      end
  end.

Definition best_generalize (j : config) (cands : list (config * nat)) : option (gen_result * nat) :=
  match best_generalize_with generalize_nontrivial j cands with
  | Some r => Some r
  | None => best_generalize_with generalize_raw j cands
  end.

(* A first fuelled supercompiler skeleton.

   This constructs a cyclic graph of configurations:
   - vertices are fresh natural numbers
   - labels are judgement configurations
   - successors are the driven/generalized continuations

   It does not yet construct the final *term* residual graph (ReadOff builder).
   The intent is to connect this config-graph to the cyclic proof layer (or to a
   residual term graph) once folding/backlink substitution evidence is pinned
   down.
*)

Record cfg_builder : Type := {
  cb_next : nat;
  cb_label : gmap nat config;
  cb_succ : gmap nat (list nat);
  (** If a vertex [v] is an *instance* of a generalised vertex [w] (so
      [cb_succ[v] = [w]]), record the instantiation substitution list here.

      Operationally, residualisation will turn this into an application
      `apps (residual w) (cb_inst[v])`.
  *)
  cb_inst : gmap nat (list tm);
  (** For a generalised configuration vertex, record the list of hole types
      (the prefix context added by anti-unification). Residualisation uses these
      to build a lambda-prefix on the residual definition. *)
  cb_holes : gmap nat (list tm);
}.

Definition cb_empty : cfg_builder :=
  {| cb_next := 0; cb_label := ∅; cb_succ := ∅; cb_inst := ∅; cb_holes := ∅ |}.

Definition cb_fresh (b : cfg_builder) : nat * cfg_builder :=
  let v := b.(cb_next) in
  (v,
    {| cb_next := S v;
       cb_label := b.(cb_label);
       cb_succ := b.(cb_succ);
       cb_inst := b.(cb_inst);
       cb_holes := b.(cb_holes) |}).

Definition cb_put_label (v : nat) (j : config) (b : cfg_builder) : cfg_builder :=
  {| cb_next := b.(cb_next);
     cb_label := <[v := j]> b.(cb_label);
     cb_succ := b.(cb_succ);
     cb_inst := b.(cb_inst);
     cb_holes := b.(cb_holes) |}.

Definition cb_put_succ (v : nat) (succs : list nat) (b : cfg_builder) : cfg_builder :=
  {| cb_next := b.(cb_next);
     cb_label := b.(cb_label);
     cb_succ := <[v := succs]> b.(cb_succ);
     cb_inst := b.(cb_inst);
     cb_holes := b.(cb_holes) |}.

Definition cb_put_inst (v : nat) (σ : list tm) (b : cfg_builder) : cfg_builder :=
  {| cb_next := b.(cb_next);
     cb_label := b.(cb_label);
     cb_succ := b.(cb_succ);
     cb_inst := <[v := σ]> b.(cb_inst);
     cb_holes := b.(cb_holes) |}.

Definition cb_put_holes (v : nat) (hs : list tm) (b : cfg_builder) : cfg_builder :=
  {| cb_next := b.(cb_next);
     cb_label := b.(cb_label);
     cb_succ := b.(cb_succ);
     cb_inst := b.(cb_inst);
     cb_holes := <[v := hs]> b.(cb_holes) |}.

Record sc_state : Type := {
  sc_builder : cfg_builder;
  sc_memo : list (config * nat);
}.

Definition sc_init : sc_state :=
  {| sc_builder := cb_empty; sc_memo := [] |}.

Definition memo_add (j : config) (v : nat) (st : sc_state) : sc_state :=
  {| sc_builder := st.(sc_builder);
     sc_memo := (j, v) :: st.(sc_memo) |}.

Definition sc_alloc (j : config) (st : sc_state) : nat * sc_state :=
  let '(v, b1) := cb_fresh st.(sc_builder) in
  let b2 := cb_put_label v j b1 in
  (v, {| sc_builder := b2; sc_memo := (j, v) :: st.(sc_memo) |}).

Fixpoint supercompile_cfg (fuel : nat) (Σenv : Ty.env) (j : config) (st : sc_state)
  {struct fuel} : option (nat * sc_state) :=
  let j := canon_config (norm_config memo_norm_fuel Σenv j) in
  match memo_lookup j st.(sc_memo) with
  | Some v => Some (v, st)
  | None =>
      let '(v, st1) := sc_alloc j st in
      match fuel with
      | 0 => Some (v, st1)
      | S fuel' =>
          let fix compile_succs (js : list config) (st0 : sc_state)
              {struct js} : option (list nat * sc_state) :=
              match js with
              | [] => Some ([], st0)
              | j0 :: js0 =>
                  match supercompile_cfg fuel' Σenv j0 st0 with
                  | None => None
                  | Some (w, stw) =>
                      match compile_succs js0 stw with
                      | None => None
                      | Some (ws, st2) => Some (w :: ws, st2)
                      end
                  end
              end
          in
          (* check whistle/generalisation against the previous memo (not including [j]) *)
          let cands := whistle_candidates fuel' j st.(sc_memo) in
          match best_generalize j cands with
          | Some (g, v_prev) =>
              (* Allocate the generalised configuration vertex. *)
              let '(vg, stg0) := sc_alloc g.(gen_j) st1 in
              let bg1 := cb_put_holes vg g.(gen_holes) stg0.(sc_builder) in
              (* Patch the previous and current vertices to call the generalised one. *)
              let bg2 := cb_put_succ v_prev [vg] bg1 in
              let bg3 := cb_put_inst v_prev g.(gen_sub1) bg2 in
              let bg4 := cb_put_succ v [vg] bg3 in
              let bg5 := cb_put_inst v g.(gen_sub2) bg4 in
              let stg1 := {| sc_builder := bg5; sc_memo := stg0.(sc_memo) |} in
              (* Explore successors of the generalised node. *)
              let nextg := drive_step Σenv g.(gen_j) in
              match compile_succs nextg stg1 with
              | None => Some (v, stg1)
              | Some (vsg, stg2) =>
                  let b' := cb_put_succ vg vsg stg2.(sc_builder) in
                  Some (v, {| sc_builder := b'; sc_memo := stg2.(sc_memo) |})
              end
          | None =>
              let next := drive_step Σenv j in
              match compile_succs next st1 with
              | None => Some (v, st1)
              | Some (vs, st2) =>
                  let b' := cb_put_succ v vs st2.(sc_builder) in
                  Some (v, {| sc_builder := b'; sc_memo := st2.(sc_memo) |})
              end
          end
      end
  end.

Definition supercompile_jTy (fuel : nat) (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option (nat * cfg_builder) :=
  match supercompile_cfg fuel Σenv (C.jTy Γ t A) sc_init with
  | None => None
  | Some (v, st) => Some (v, st.(sc_builder))
  end.

(** * Residualisation

    Turn the configuration graph (built by [supercompile_cfg]) into a residual
    term. This is *graph readback* only: it reconstructs `case` nodes for
    case-splitting vertices, and follows single-successor rewrite vertices.

    NOTE: this is not yet "full" residualisation with explicit folding into
    `tFix` binders. Cycles are currently handled by bounding recursion with fuel.
    The next step is to introduce back-links and extract them into `tFix` using
    the existing ReadOff/Extract pipeline.
*)

Fixpoint mk_lams (As : list tm) (body : tm) : tm :=
  match As with
  | [] => body
  | A :: As => tLam A (mk_lams As body)
  end.

Definition lookup_label (b : cfg_builder) (v : nat) : option config := b.(cb_label) !! v.
Definition lookup_succ (b : cfg_builder) (v : nat) : option (list nat) := b.(cb_succ) !! v.
Definition lookup_inst (b : cfg_builder) (v : nat) : option (list tm) := b.(cb_inst) !! v.
Definition lookup_holes (b : cfg_builder) (v : nat) : list tm := default [] (b.(cb_holes) !! v).

(** Residualise with folding for all memo back-edges.

    We treat each configuration vertex as a potential recursive definition.

    During readback, if we encounter a vertex we have already residualised, we
    fold it to a variable (rather than re-expanding it). If it is not yet bound,
    we introduce a `tFix` binder for it.

    This is a computational readback analogous to `Transform.Extract.extract_v`:
    it synthesizes nested `tFix` binders on-demand.

    NOTE: this is still not as good as SCC-based residualisation (which would
    avoid unnecessary nested `tFix`), but it correctly handles all memo back
    edges without any domain-specific rewrite laws.
*)

Definition fix_env : Type := gmap nat nat.

Definition env_shift (ρ : fix_env) : fix_env := fmap S ρ.

Fixpoint env_shift_n (n : nat) (ρ : fix_env) : fix_env :=
  match n with
  | 0 => ρ
  | S n => env_shift_n n (env_shift ρ)
  end.

Fixpoint residualise_cfg
    (fuel : nat) (Σenv : Ty.env) (b : cfg_builder)
    (v : nat) (depth : nat) (ρ : fix_env) {struct fuel} : tm :=
  match fuel with
  | 0 => tVar 0
  | S fuel' =>
      match ρ !! v with
      | Some k => tVar k
      | None =>
          match lookup_label b v with
          | Some (C.jTy _Γ _t A) =>
              let holes := lookup_holes b v in
              let n := length holes in
              let ρ0 := <[v := 0]> (env_shift ρ) in
              let ρ' := env_shift_n n ρ0 in
              let holes' := map (shift (S depth) 0) holes in
              let body_core := residualise_cfg_core fuel' Σenv b v (S depth + n) ρ' in
              let body := mk_lams holes' body_core in
              tFix (shift depth 0 A) body
          | _ => tVar 0
          end
      end
  end

with residualise_cfg_core
    (fuel : nat) (Σenv : Ty.env) (b : cfg_builder)
    (v : nat) (depth : nat) (ρ : fix_env) {struct fuel} : tm :=
  match fuel with
  | 0 => tVar 0
  | S fuel' =>
      match lookup_label b v with
      | None => tVar 0
      | Some (C.jTy _Γ t A0) =>
          match lookup_succ b v with
          | None => shift depth 0 t
          | Some [] => shift depth 0 t
          | Some [w] =>
              match lookup_inst b v with
              | Some σ =>
                  Cbn.apps (residualise_cfg fuel' Σenv b w depth ρ) (map (shift depth 0) σ)
              | None =>
                  match t with
                  | tRoll ind c [a] => tRoll ind c [residualise_cfg fuel' Σenv b w depth ρ]
                  | _ => residualise_cfg fuel' Σenv b w depth ρ
                  end
              end
          | Some ws =>
              match t with
              | tCase ind (tVar x) Cmot brs =>
                  match StrictPos.lookup_ind Σenv ind with
                  | None => shift depth 0 t
                  | Some ΣI =>
                      let nctors := length (StrictPos.ind_ctors ΣI) in
                      let cs := seq 0 nctors in
                      let brs_res :=
                        map
                          (fun c =>
                             match CC.ctor_arg_tys Σenv ind c with
                             | None =>
                                 match nth_error brs c with
                                 | Some br => shift depth 0 br
                                 | None => tVar 0
                                 end
                             | Some tys =>
                                 let n := length tys in
                                 let tys' := map (shift depth 0) tys in
                                 match nth_error ws c with
                                 | Some w =>
                                     mk_lams tys'
                                       (residualise_cfg fuel' Σenv b w (depth + n)
                                          (env_shift_n n ρ))
                                 | None =>
                                     match nth_error brs c with
                                     | Some br => shift depth 0 br
                                     | None => tVar 0
                                     end
                                 end
                             end)
                          cs
                      in
                      tCase ind (tVar (x + depth)) (shift depth 0 A0) brs_res
                  end
              | _ => shift depth 0 t
              end
          end
      | Some _ => tVar 0
      end
  end.

(** * SCC analysis (cfg graph)

    We use SCCs to define a simple canonicalisation: collapse every SCC to a
    chosen representative vertex.

    This is a lightweight step toward SCC-canonical residualisation.
*)

Definition succs_of (b : cfg_builder) (v : nat) : list nat :=
  default [] (lookup_succ b v).

Fixpoint mem_nat (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => Nat.eqb x y || mem_nat x ys
  end.

Fixpoint add_nat (x : nat) (xs : list nat) : list nat :=
  if mem_nat x xs then xs else x :: xs.

Fixpoint dfs_postorder
    (fuel : nat) (b : cfg_builder)
    (v : nat) (seen : list nat) : list nat * list nat :=
  match fuel with
  | 0 => (seen, [])
  | S fuel' =>
      if mem_nat v seen then (seen, [])
      else
        let seen1 := v :: seen in
        let fix go (vs : list nat) (seen0 : list nat) : list nat * list nat :=
          match vs with
          | [] => (seen0, [])
          | w :: ws =>
              let '(seen1, out1) := dfs_postorder fuel' b w seen0 in
              let '(seen2, out2) := go ws seen1 in
              (seen2, out1 ++ out2)
          end
        in
        let '(seen2, outs) := go (succs_of b v) seen1 in
        (seen2, outs ++ [v])
  end.

Definition reverse_edges (n : nat) (b : cfg_builder) : gmap nat (list nat) :=
  let fix add_rev (v : nat) (ws : list nat) (m : gmap nat (list nat)) : gmap nat (list nat) :=
    match ws with
    | [] => m
    | w :: ws =>
        let prev := default [] (m !! w) in
        add_rev v ws (<[w := v :: prev]> m)
    end
  in
  let fix loop (v : nat) (m : gmap nat (list nat)) : gmap nat (list nat) :=
    match v with
    | 0 => m
    | S v' =>
        let m' := add_rev v' (succs_of b v') m in
        loop v' m'
    end
  in
  loop n (∅ : gmap nat (list nat)).

Fixpoint dfs_collect
    (fuel : nat) (rev : gmap nat (list nat))
    (v : nat) (seen : list nat) : list nat * list nat :=
  match fuel with
  | 0 => (seen, [])
  | S fuel' =>
      if mem_nat v seen then (seen, [])
      else
        let seen1 := v :: seen in
        let vs := default [] (rev !! v) in
        let fix go (ws : list nat) (seen0 : list nat) : list nat * list nat :=
          match ws with
          | [] => (seen0, [])
          | w :: ws =>
              let '(seen1, out1) := dfs_collect fuel' rev w seen0 in
              let '(seen2, out2) := go ws seen1 in
              (seen2, out1 ++ out2)
          end
        in
        let '(seen2, outs) := go vs seen1 in
        (seen2, v :: outs)
  end.

Fixpoint kosaraju_scc
    (fuel : nat) (n : nat) (b : cfg_builder) : list (list nat) :=
  let revg := reverse_edges n b in
  (* get a postorder stack by exploring all vertices *)
  let fix post_all (v : nat) (seen : list nat) (stack : list nat) : list nat * list nat :=
    match v with
    | 0 => (seen, stack)
    | S v' =>
        let '(seen1, stack1) := dfs_postorder fuel b v' seen in
        post_all v' seen1 (stack ++ stack1)
    end
  in
  let '(_seen, stack) := post_all n [] [] in
  (* second pass on reverse graph in reverse stack order *)
  let fix pass2 (stk : list nat) (seen : list nat) : list (list nat) :=
    match stk with
    | [] => []
    | v :: stk' =>
        if mem_nat v seen then pass2 stk' seen
        else
          let '(seen1, comp) := dfs_collect fuel revg v seen in
          comp :: pass2 stk' seen1
    end
  in
  pass2 (List.rev stack) [].

Fixpoint min_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | [x] => x
  | x :: xs => Nat.min x (min_list xs)
  end.

Definition scc_rep_map (sccs : list (list nat)) : gmap nat nat :=
  let fix add_scc (comp : list nat) (rep : nat) (m : gmap nat nat) : gmap nat nat :=
    match comp with
    | [] => m
    | v :: vs => add_scc vs rep (<[v := rep]> m)
    end
  in
  let fix loop (cs : list (list nat)) (m : gmap nat nat) : gmap nat nat :=
    match cs with
    | [] => m
    | comp :: cs =>
        let rep := min_list comp in
        loop cs (add_scc comp rep m)
    end
  in
  loop sccs (∅ : gmap nat nat).

Definition canon_vertex (m : gmap nat nat) (v : nat) : nat :=
  default v (m !! v).

Definition canon_succs (m : gmap nat nat) (vs : list nat) : list nat :=
  nub_nat (map (canon_vertex m) vs).

Definition canon_cfg_builder_scc (b : cfg_builder) : cfg_builder :=
  let n := cb_next b in
  let sccs := kosaraju_scc (2 * (n + 1)) n b in
  let m := scc_rep_map sccs in
  let fix loop (v : nat) (succm : gmap nat (list nat)) : gmap nat (list nat) :=
    match v with
    | 0 => succm
    | S v' =>
        let vs := canon_succs m (succs_of b v') in
        loop v' (<[v' := vs]> succm)
    end
  in
  {| cb_next := cb_next b;
     cb_label := cb_label b;
     cb_succ := loop n (∅ : gmap nat (list nat));
     cb_inst := cb_inst b;
     cb_holes := cb_holes b |}.

(** * Global progress / trace-condition check (cfg graph) *)

Definition is_progress_vertex (b : cfg_builder) (v : nat) : bool :=
  match lookup_label b v, lookup_succ b v with
  | Some (C.jTy _Γ (tCase _I (tVar _x) _Cmot _brs) _A), Some succs =>
      Nat.ltb 1 (length succs)
  | _, _ => false
  end.

Definition nonprogress_succs_of (b : cfg_builder) (v : nat) : list nat :=
  if is_progress_vertex b v then [] else succs_of b v.

Definition cfg_builder_nonprogress (b : cfg_builder) : cfg_builder :=
  let n := cb_next b in
  let fix loop (v : nat) (succm : gmap nat (list nat)) : gmap nat (list nat) :=
    match v with
    | 0 => succm
    | S v' => loop v' (<[v' := nonprogress_succs_of b v']> succm)
    end
  in
  {| cb_next := cb_next b;
     cb_label := cb_label b;
     cb_succ := loop n (∅ : gmap nat (list nat));
     cb_inst := cb_inst b;
     cb_holes := cb_holes b |}.

Definition has_nonprogress_cycle_scc (b : cfg_builder) : bool :=
  let bnp := cfg_builder_nonprogress b in
  let n := cb_next bnp in
  let sccs := kosaraju_scc (2 * (n + 1)) n bnp in
  existsb
    (fun comp =>
       match comp with
       | [] => false
       | [v] => mem_nat v (succs_of bnp v)
       | _ :: _ :: _ => true
       end)
    sccs.

Fixpoint reach_depth (k : nat) (b : cfg_builder) (v : nat) : list nat :=
  match k with
  | 0 => succs_of b v
  | S k' =>
      let succs := succs_of b v in
      nub_nat (succs ++
        fold_right (fun w acc => reach_depth k' b w ++ acc) [] succs)
  end.

Definition has_cycle_by_depth (k : nat) (b : cfg_builder) (n : nat) : bool :=
  existsb (fun v => mem_nat v (reach_depth k b v)) (seq 0 n).

Definition has_nonprogress_cycle (b : cfg_builder) : bool :=
  let bnp := cfg_builder_nonprogress b in
  let n := cb_next bnp in
  match n with
  | 0 => false
  | S _ => has_cycle_by_depth n bnp n
  end.

Definition trace_condition_ok (b : cfg_builder) : bool :=
  negb (has_nonprogress_cycle b).

(** Supercompilation wrapper that rejects graphs failing the progress condition. *)
Definition supercompile_jTy_tc (fuel : nat) (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm)
    : option (nat * cfg_builder) :=
  match supercompile_jTy fuel Σenv Γ t A with
  | None => None
  | Some (root, b) => if trace_condition_ok b then Some (root, b) else None
  end.

Definition residualise_jTy (fuel_sc fuel_res : nat)
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option tm :=
  match supercompile_jTy_tc fuel_sc Σenv Γ t A with
  | None => None
  | Some (root, b) => Some (residualise_cfg fuel_res Σenv b root 0 (∅ : fix_env))
  end.

Definition option_tm_eqb (o1 o2 : option tm) : bool :=
  match o1, o2 with
  | None, None => true
  | Some t1, Some t2 => tm_eqb t1 t2
  | _, _ => false
  end.

Fixpoint residualise_jTy_fp
    (passes fuel_sc fuel_res : nat)
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option tm :=
  match passes with
  | 0 => residualise_jTy fuel_sc fuel_res Σenv Γ t A
  | S passes' =>
      match residualise_jTy fuel_sc fuel_res Σenv Γ t A with
      | None => None
      | Some t' =>
          if tm_eqb t t' then Some t'
          else residualise_jTy_fp passes' fuel_sc fuel_res Σenv Γ t' A
      end
  end.

Definition residualise_jTy_scc (fuel_sc fuel_res : nat)
    (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option tm :=
  match supercompile_jTy_tc fuel_sc Σenv Γ t A with
  | None => None
  | Some (root, b) =>
      let b' := canon_cfg_builder_scc b in
      Some (residualise_cfg fuel_res Σenv b' root 0 (∅ : fix_env))
  end.
