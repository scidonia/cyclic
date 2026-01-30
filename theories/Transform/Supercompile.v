From Stdlib Require Import List Bool Arith Utf8.
From stdpp Require Import gmap.

From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
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
        | tCase I scrut C brs =>
            (* Try case-of-constructor reduction first *)
            let scrut' := drive_under_binders fuel' scrut in
            tCase I scrut'
                  (drive_under_binders fuel' C)
                  (map (drive_under_binders fuel') brs)
        | tRoll I c args =>
            tRoll I c (map (drive_under_binders fuel') args)
        | tInd I args =>
            tInd I (map (drive_under_binders fuel') args)
        | _ => t
        end
      in t'
  end.

Definition default_rewrites (Σenv : Ty.env) : list rewrite_step :=
  [BetaReduce.whnf_reduce 100;         (* Reduce to WHNF at head *)
   CC.commute_case_case_once_typed Σenv;
   CC.propagate_motive_once;
   BetaReduce.full_normalize 50        (* Full normalization under binders *)
  ].

Definition drive_step (Σenv : Ty.env) (j : config) : list config :=
  match j with
  | C.jTy Γ t A => map (fun u => C.jTy Γ u A) (drive_terms (default_rewrites Σenv) t)
  | _ => []
  end.

(* A computable approximation of the embedding/whistle relation.
   The Prop-level relation lives in `theories/Progress/Embedding.v`.
   For now we use a fuelled boolean check with the same intended shape:
   the *first* argument is the potentially larger term/judgement. *)

Fixpoint emb_list_b (fuel : nat) (embA : tm -> tm -> bool) (xs ys : list tm) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      match xs, ys with
      | [], [] => true
      | [], _ => false
      | _ :: _, [] => false
      | x :: xs', y :: ys' =>
          (embA x y && emb_list_b fuel' embA xs' ys')
          || emb_list_b fuel' embA xs' ys
      end
  end.

Fixpoint emb_tm_b (fuel : nat) (t u : tm) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      if tm_eqb t u then true
      else
        match t with
        | tPi A B =>
            emb_tm_b fuel' A u
            || emb_tm_b fuel' B u
            || match u with
               | tPi A' B' => emb_tm_b fuel' A A' && emb_tm_b fuel' B B'
               | _ => false
               end
        | tLam A t0 =>
            emb_tm_b fuel' A u
            || emb_tm_b fuel' t0 u
            || match u with
               | tLam A' t0' => emb_tm_b fuel' A A' && emb_tm_b fuel' t0 t0'
               | _ => false
               end
        | tApp t1 t2 =>
            emb_tm_b fuel' t1 u
            || emb_tm_b fuel' t2 u
            || match u with
               | tApp u1 u2 => emb_tm_b fuel' t1 u1 && emb_tm_b fuel' t2 u2
               | _ => false
               end
        | tFix A t0 =>
            emb_tm_b fuel' A u
            || emb_tm_b fuel' t0 u
            || match u with
               | tFix A' t0' => emb_tm_b fuel' A A' && emb_tm_b fuel' t0 t0'
               | _ => false
               end
        | tRoll ind ctor params recs =>
            (existsb (fun p => emb_tm_b fuel' p u) params)
            || (existsb (fun r => emb_tm_b fuel' r u) recs)
            || match u with
               | tRoll ind' ctor' params' recs' =>
                   Nat.eqb ind ind'
                   && Nat.eqb ctor ctor'
                   && emb_list_b fuel' (emb_tm_b fuel') params params'
                   && emb_list_b fuel' (emb_tm_b fuel') recs recs'
               | _ => false
               end
        | tCase ind scrut C0 brs =>
            emb_tm_b fuel' scrut u
            || emb_tm_b fuel' C0 u
            || existsb (fun br => emb_tm_b fuel' br u) brs
            || match u with
               | tCase ind' scrut' C0' brs' =>
                   Nat.eqb ind ind'
                   && emb_tm_b fuel' scrut scrut'
                   && emb_tm_b fuel' C0 C0'
                   && emb_list_b fuel' (emb_tm_b fuel') brs brs'
               | _ => false
               end
        | _ => false
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

Fixpoint whistle_find (fuel : nat) (j : config) (memo : list (config * nat)) : option config :=
  match memo with
  | [] => None
  | (j_prev, _) :: memo =>
      if emb_judgement_b fuel j j_prev then Some j_prev else whistle_find fuel j memo
  end.

(* Generalisation wrapper: we reuse the existing computational anti-unifier.
   This is deliberately lightweight (typedness proofs can follow later). *)

Record gen_result : Type := {
  gen_holes : list tm;
  gen_j : config;
  gen_sub1 : list tm;
  gen_sub2 : list tm;
}.

Definition generalize (j1 j2 : config) : option gen_result :=
  match PU.anti_unify_judgement j1 j2 with
  | None => None
  | Some r =>
      Some
        {| gen_holes := PU.auJ_holes r;
           gen_j := PU.auJ_gen r;
           gen_sub1 := PU.auJ_sub1 r;
           gen_sub2 := PU.auJ_sub2 r |}
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
}.

Definition cb_empty : cfg_builder :=
  {| cb_next := 0; cb_label := ∅; cb_succ := ∅ |}.

Definition cb_fresh (b : cfg_builder) : nat * cfg_builder :=
  let v := b.(cb_next) in
  (v, {| cb_next := S v; cb_label := b.(cb_label); cb_succ := b.(cb_succ) |}).

Definition cb_put_label (v : nat) (j : config) (b : cfg_builder) : cfg_builder :=
  {| cb_next := b.(cb_next);
     cb_label := <[v := j]> b.(cb_label);
     cb_succ := b.(cb_succ) |}.

Definition cb_put_succ (v : nat) (succs : list nat) (b : cfg_builder) : cfg_builder :=
  {| cb_next := b.(cb_next);
     cb_label := b.(cb_label);
     cb_succ := <[v := succs]> b.(cb_succ) |}.

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

Definition choose_next (fuel : nat) (Σenv : Ty.env) (j : config) (memo : list (config * nat)) : list config :=
  match whistle_find fuel j memo with
  | Some j_prev =>
      match generalize j_prev j with
      | Some g => [g.(gen_j)]
      | None => drive_step Σenv j
      end
  | None => drive_step Σenv j
  end.

Fixpoint supercompile_cfg (fuel : nat) (Σenv : Ty.env) (j : config) (st : sc_state)
  {struct fuel} : option (nat * sc_state) :=
  match memo_lookup j st.(sc_memo) with
  | Some v => Some (v, st)
  | None =>
      let '(v, st1) := sc_alloc j st in
      match fuel with
      | 0 => Some (v, st1)
      | S fuel' =>
          let next := choose_next fuel' Σenv j st.(sc_memo) in
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
          match compile_succs next st1 with
          | None => Some (v, st1)
          | Some (vs, st2) =>
              let b' := cb_put_succ v vs st2.(sc_builder) in
              Some (v, {| sc_builder := b'; sc_memo := st2.(sc_memo) |})
          end
      end
  end.

Definition supercompile_jTy (fuel : nat) (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option (nat * cfg_builder) :=
  match supercompile_cfg fuel Σenv (C.jTy Γ t A) sc_init with
  | None => None
  | Some (v, st) => Some (v, st.(sc_builder))
  end.
