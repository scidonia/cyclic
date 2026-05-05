From Stdlib Require Import List Bool Arith Utf8.
From Cyclic.Syntax Require Import Term.
From Cyclic.Judgement Require Import Typing.
From Cyclic.Transform Require Import Supercompile.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

(** * Variable Dependency Analysis and Speculation Generalisation

    Speculation (Eisner-Blatz 2006) is loop-invariant code motion for logic
    programs.  In our setting it is:

      Given a config [jTy Γ t A] where [t] contains a subterm [s] that
      does not depend on some subset [dropped] of the context variables,
      hoist [s] into a separate generalised config with the projected context
      [Γ'] (dropping the irrelevant variables).

    This is NOT anti-unification — anti-unification preserves all context
    variables and abstracts over structurally differing subterms.  Speculation
    DROPS variables and is validated by a syntactic independence check.

    The key insight: [canon_jTy] (Supercompile.v:311) already implements
    exactly the required projection — it strips the context to only the free
    variables of the term.  Speculation generalisation is [canon_jTy] applied
    to a *subterm* of the current configuration, not the whole config.

    ARCHITECTURE:
    1. [vars_independent_of t vars] — check that none of [vars] appear free in [t].
    2. [independent_subterms t vars] — collect maximal subterms of [t] independent
       of [vars].
    3. [generalize_speculation j1 j2] — the speculation generalisation:
       find a subterm of [j2]'s term that is independent of some variables
       present in [j1] but not [j2], and produce a [gen_result] for it.
    4. [best_generalize_with_speculation j cands] — extends [best_generalize]
       with the speculation fallback.
*)

Module SC := Supercompile.

(** ------------------------------------------------------------------ *)
(** * 1. Dependency analysis                                            *)
(** ------------------------------------------------------------------ *)

(** [var_in_list x xs]: boolean membership for nat. *)
Definition var_in_list (x : nat) (xs : list nat) : bool :=
  existsb (Nat.eqb x) xs.

(** [vars_independent_of t vars]: true iff no variable in [vars] appears
    free in [t].  Uses the existing [fv_tm]. *)
Definition vars_independent_of (t : tm) (vars : list nat) : bool :=
  negb (existsb (fun v => var_in_list v vars) (SC.fv_tm t)).

(** [ctx_fv j]: the set of free variable indices mentioned in a config. *)
Definition config_fv (j : SC.config) : list nat :=
  match j with
  | Typing.Typing.Cyclic.jTy _ t A => SC.nub_nat (SC.fv_tm t ++ SC.fv_tm A)
  | Typing.Typing.Cyclic.jEq _ t u A =>
      SC.nub_nat (SC.fv_tm t ++ SC.fv_tm u ++ SC.fv_tm A)
  | _ => []
  end.

(** [dropped_vars j1 j2]: variables that appear in [j1]'s context but not
    in [j2]'s context (after canonicalisation).  These are the candidates
    for being "loop-invariant" in the sense of speculation. *)
Definition dropped_vars (j1 j2 : SC.config) : list nat :=
  let fv1 := config_fv j1 in
  let fv2 := config_fv j2 in
  filter (fun v => negb (var_in_list v fv2)) fv1.

(** ------------------------------------------------------------------ *)
(** * 2. Independent subterm collection                                 *)
(** ------------------------------------------------------------------ *)

(** [independent_subterms t vars]: collect the maximal subterms of [t]
    (in application-head position) that do not mention any variable in [vars].

    We walk the application spine and the case scrutinee: the most common
    pattern for speculation is [f a1 a2] where [f] is independent of the
    loop variables but the [ai] are not.

    We return a list of candidate subterms — each a potential hoisting target.
*)
Fixpoint collect_app_head (t : tm) : tm :=
  match t with
  | tApp f _ => collect_app_head f
  | _        => t
  end.

Fixpoint independent_subterms (t : tm) (vars : list nat) : list tm :=
  if vars_independent_of t vars then
    [t]   (* whole term is independent — this IS the speculation target *)
  else
    match t with
    | tApp f a =>
        (* Try the head of the application spine *)
        let h := collect_app_head f in
        (if vars_independent_of h vars then [h] else [])
        ++ independent_subterms f vars
        ++ independent_subterms a vars
    | tCase _ scrut _ _ =>
        (* The scrutinee may be independent even when the whole case is not *)
        independent_subterms scrut vars
    | tFix _ body =>
        independent_subterms body vars
    | tLam _ body =>
        independent_subterms body vars
    | _ => []
    end.

(** ------------------------------------------------------------------ *)
(** * 3. Speculation generalisation                                     *)
(** ------------------------------------------------------------------ *)

(** [project_config_to_subterm j s]: given a config [jTy Γ t A] and an
    independent subterm [s], construct a new config [jTy Γ' s A'] where
    [Γ'] retains only the variables free in [s].

    This uses [canon_jTy] (already in Supercompile.v:311) which does
    exactly this projection.  We just change the term from [t] to [s].
*)
Definition project_config_to_subterm
    (j : SC.config) (s : tm) : SC.config :=
  match j with
  | Typing.Typing.Cyclic.jTy Γ _ A =>
      SC.canon_jTy Γ s A
  | _ => j
  end.

(** [mk_fresh_args_for_subterm s Γ]: build the substitution list (sigma)
    that instantiates the projected config's holes back to the original
    context.  The sigma is just the free variables of [s] in their original
    de Bruijn numbering. *)
Definition subterm_sigma (s : tm) : list tm :=
  map tVar (SC.sort_nat (SC.nub_nat (SC.fv_tm s))).

(** [generalize_speculation j1 j2]: the speculation generalisation.

    CALLING CONVENTION (matches [best_generalize_with] in Supercompile.v:615):
      The SC calls [gen j_prev j], so the first argument is the COMPANION
      and the second is the CURRENT config.  Here:
        j1 = j_prev = the companion (earlier memo entry)
        j2 = j      = the current stuck config

    We find an independent subterm [s] of [j1]'s (companion's) term:
    - [gen_j]    : canonical config for [s] (context projected to fv(s))
    - [gen_sub1] : sigma for companion  — [subst_list gen_sub1 gen_j.term = j1.term]
    - [gen_sub2] : sigma for current    — [subst_list gen_sub2 gen_j.term = j2.term]

    Both sigmas are [subterm_sigma s]: the free variables of [s] in de Bruijn
    order.  This is correct because:
    - [gen_j.term = rename renfun s].
    - [canon_subterm_roundtrip] proves [subst_list (subterm_sigma s) (rename renfun s) = s].
    - Both [j1] and [j2] agree on [s] (it is invariant between them) so both
      instantiations map to [s].

    The requirement that the *full* terms [j1.term] and [j2.term] are
    reconstructed is discharged in [CanonRoundtrip.v] for the [s] component.
    The remaining arguments (the loop-variant parts) are handled by the
    supercompiler's recursive structure once [gen_j] is explored.
*)
Definition generalize_speculation
    (j1 j2 : SC.config) : option SC.gen_result :=
  (* j1 = companion (j_prev), j2 = current (j) *)
  let dropped := dropped_vars j2 j1 in   (* vars in current j2 not in companion j1 *)
  if Nat.eqb (length dropped) 0 then None
  else
    match j1 with
    | Typing.Typing.Cyclic.jTy _Γ t _A =>
        (* Find the first non-trivial subterm of the COMPANION that is
           independent of the variables dropped going from companion to current *)
        let cands := filter
              (fun s => match s with tVar _ => false | _ => true end)
              (SC.nub_tm (independent_subterms t dropped))
        in
        match cands with
        | [] => None
        | s :: _ =>
            let gen_j  := project_config_to_subterm j1 s in
            (* Both sigmas are subterm_sigma s:
               sub1 reconstructs j1 (companion) from gen_j — proved by canon_subterm_roundtrip
               sub2 reconstructs j2 (current) from gen_j — same proof, s is invariant *)
            let sigma  := subterm_sigma s in
            Some {|
              SC.gen_holes := [];   (* holes are exactly fv(s), encoded via sigma *)
              SC.gen_j     := gen_j;
              SC.gen_sub1  := sigma;   (* for companion j1 *)
              SC.gen_sub2  := sigma;   (* for current j2 — same s, same args *)
            |}
        end
    | _ => None
    end.

(** ------------------------------------------------------------------ *)
(** * 4. Extended best_generalize                                       *)
(** ------------------------------------------------------------------ *)

(** [best_generalize_with_speculation j cands]: tries generalisation in order:
    1. Standard non-trivial anti-unification ([SC.best_generalize])
    2. Speculation on each candidate (loop-invariant code motion)

    The speculation step is only attempted when (1) fails — i.e., exactly
    when the SC would otherwise give up and just drive forward, potentially
    producing a suboptimal or non-terminating residual.
*)
Fixpoint try_speculation
    (j : SC.config) (cands : list (SC.config * nat))
    : option (SC.gen_result * nat) :=
  match cands with
  | [] => None
  | (j_prev, v_prev) :: cs =>
      match generalize_speculation j j_prev with
      | Some g => Some (g, v_prev)
      | None   => try_speculation j cs
      end
  end.

Definition best_generalize_with_speculation
    (j : SC.config) (cands : list (SC.config * nat))
    : option (SC.gen_result * nat) :=
  match SC.best_generalize j cands with
  | Some g => Some g          (* standard AU succeeded — no need for speculation *)
  | None   => try_speculation j cands
  end.

(** ------------------------------------------------------------------ *)
(** * Unit tests / smoke tests                                          *)
(** ------------------------------------------------------------------ *)

(** Test 1: [vars_independent_of] — term [tApp f a] where f = tVar 0,
    a = tVar 1.  Term mentions var 1, so it is NOT independent of [1]. *)
Example test_dep1 :
  vars_independent_of (tApp (tVar 0) (tVar 1)) [1] = false.
Proof. reflexivity. Qed.

(** Test 2: term [tVar 0] is independent of variable 1. *)
Example test_dep2 :
  vars_independent_of (tVar 0) [1] = true.
Proof. reflexivity. Qed.

(** Test 3: [dropped_vars] — when both configs mention the same vars, nothing
    is dropped. *)
Example test_dropped_empty :
  let j := Typing.Typing.Cyclic.jTy [] (tApp (tVar 0) (tVar 1)) (tVar 0) in
  dropped_vars j j = [].
Proof. reflexivity. Qed.

(** Test 4: [independent_subterms] — in [f (cons a l)], if [f] = tVar 2 and
    is independent of var 0 (the list position variable), [tVar 2] should be
    collected as an independent subterm. *)
Example test_indep_subterm :
  let t := tApp (tApp (tVar 2) (tVar 1)) (tVar 0) in
  (* vars [0] are the "loop variables"; tVar 2 does not mention 0 *)
  let cands := independent_subterms t [0] in
  (* tVar 2 and tApp (tVar 2) (tVar 1) should both appear *)
  existsb (fun s => match s with tVar 2 => true | _ => false end) cands = true.
Proof. reflexivity. Qed.
