From Stdlib Require Import List Bool Arith Utf8.

From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import BetaReduce.
From Cyclic.Progress Require Import PatternUnification.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module Ty := Typing.Typing.
Module C := Typing.Typing.Cyclic.
Module PU := PatternUnification.

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

Definition default_rewrites : list rewrite_step :=
  [BetaReduce.beta_reduce_once].

Definition drive_step (_Σenv : Ty.env) (j : config) : list config :=
  match j with
  | C.jTy Γ t A => map (fun u => C.jTy Γ u A) (drive_terms default_rewrites t)
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
        | tRoll I c params recs =>
            (existsb (fun p => emb_tm_b fuel' p u) params)
            || (existsb (fun r => emb_tm_b fuel' r u) recs)
            || match u with
               | tRoll I' c' params' recs' =>
                   Nat.eqb I I'
                   && Nat.eqb c c'
                   && emb_list_b fuel' (emb_tm_b fuel') params params'
                   && emb_list_b fuel' (emb_tm_b fuel') recs recs'
               | _ => false
               end
        | tCase I scrut C0 brs =>
            emb_tm_b fuel' scrut u
            || emb_tm_b fuel' C0 u
            || existsb (fun br => emb_tm_b fuel' br u) brs
            || match u with
               | tCase I' scrut' C0' brs' =>
                   Nat.eqb I I'
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

   This does not yet build a residual term graph; instead it assigns stable node
   ids to configurations by exploring rewrites, folding by memoization, and
   using generalisation when the whistle triggers.

   The intention is that the later "graph-building" phase will replace the
   id allocation with actual `ReadOff.builder` construction. *)

Record sc_state : Type := {
  sc_next_id : nat;
  sc_memo : list (config * nat);
}.

Definition sc_init : sc_state :=
  {| sc_next_id := 0; sc_memo := [] |}.

Definition memo_add (j : config) (v : nat) (st : sc_state) : sc_state :=
  {| sc_next_id := st.(sc_next_id);
     sc_memo := (j, v) :: st.(sc_memo) |}.

Definition fresh_id (st : sc_state) : nat * sc_state :=
  let v := st.(sc_next_id) in
  (v, {| sc_next_id := S v; sc_memo := st.(sc_memo) |}).

Fixpoint supercompile_id (fuel : nat) (Σenv : Ty.env) (j : config) (st : sc_state)
  {struct fuel} : option (nat * sc_state) :=
  match memo_lookup j st.(sc_memo) with
  | Some v => Some (v, st)
  | None =>
      match fuel with
      | 0 =>
          let '(v, st1) := fresh_id st in
          Some (v, memo_add j v st1)
      | S fuel' =>
          match whistle_find (S fuel') j st.(sc_memo) with
          | Some j_prev =>
              match generalize j_prev j with
              | Some g =>
                  match supercompile_id fuel' Σenv g.(gen_j) st with
                  | None => None
                  | Some (vg, stg) => Some (vg, memo_add j vg stg)
                  end
              | None =>
                  (* Fall back to driving if we can't generalise. *)
                  match drive_step Σenv j with
                  | j1 :: _ =>
                      match supercompile_id fuel' Σenv j1 st with
                      | None => None
                      | Some (v1, st1) => Some (v1, memo_add j v1 st1)
                      end
                  | [] =>
                      let '(v, st1) := fresh_id st in
                      Some (v, memo_add j v st1)
                  end
              end
          | None =>
              match drive_step Σenv j with
              | j1 :: _ =>
                  match supercompile_id fuel' Σenv j1 st with
                  | None => None
                  | Some (v1, st1) => Some (v1, memo_add j v1 st1)
                  end
              | [] =>
                  let '(v, st1) := fresh_id st in
                  Some (v, memo_add j v st1)
              end
          end
      end
  end.

Definition supercompile_jTy (fuel : nat) (Σenv : Ty.env) (Γ : Ty.ctx) (t A : tm) : option nat :=
  option_map fst (supercompile_id fuel Σenv (C.jTy Γ t A) sc_init).
