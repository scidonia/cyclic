From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude countable gmap.

From Cyclic.Syntax Require Import Term.
From Cyclic.Transform Require Import ReadOff.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.
Module RO := ReadOff.

(**
  Extraction (stage 1)

  This module reconstructs CIC terms (with `tFix`) from the fix-free cyclic
  graph produced by `Transform.ReadOff`.

  Key points:
  - recursion in the graph is represented by `nBack` nodes
  - each `nBack` node points to a cycle target vertex `u` and a substitution
    evidence vertex `sv` (label `nSubst`)
  - we re-synthesize `tFix` binders for cycle targets using the metadata
    `b_fix_ty : gmap nat nat` recorded by read-off

  This is intentionally a computational pass; typing/proof obligations are
  handled later by the cyclic proof layer.
*)

Section Extract.
  Definition fix_env : Type := gmap nat nat.

  Definition env_shift (ρ : fix_env) : fix_env :=
    fmap S ρ.

  Fixpoint apps (t : T.tm) (us : list T.tm) : T.tm :=
    match us with
    | [] => t
    | u :: us => apps (T.tApp t u) us
    end.

  Definition lookup_node (b : RO.builder) (v : nat) : RO.node :=
    default (RO.nVar 0) (RO.b_label b !! v).

  Definition lookup_succ (b : RO.builder) (v : nat) : list nat :=
    default [] (RO.b_succ b !! v).

  Fixpoint extract_v (fuel : nat) (b : RO.builder) (ρ : fix_env) (v : nat) : T.tm :=
    match fuel with
    | 0 => T.tVar 0
    | S fuel' =>
        (* If `v` is a cycle target and not already bound in `ρ`, introduce a fix binder. *)
        match ρ !! v with
        | None =>
            match RO.b_fix_ty b !! v with
            | Some vA =>
                let A := extract_v fuel' b ρ vA in
                let ρ' := <[v := 0]> (env_shift ρ) in
                let body := extract_v fuel' b ρ' v in
                T.tFix A body
            | None =>
                extract_node fuel' b ρ v
            end
        | Some k =>
            (* The vertex is bound by an enclosing synthesized fix. Treat it as a variable. *)
            T.tVar k
        end
    end

  with extract_node (fuel : nat) (b : RO.builder) (ρ : fix_env) (v : nat) : T.tm :=
    match lookup_node b v with
    | RO.nVar x => T.tVar x
    | RO.nSort i => T.tSort i
    | RO.nPi =>
        match lookup_succ b v with
        | [vA; vB] =>
            let A := extract_v fuel b ρ vA in
            let B := extract_v fuel b (env_shift ρ) vB in
            T.tPi A B
        | _ => T.tVar 0
        end
    | RO.nLam =>
        match lookup_succ b v with
        | [vA; vt] =>
            let A := extract_v fuel b ρ vA in
            let t := extract_v fuel b (env_shift ρ) vt in
            T.tLam A t
        | _ => T.tVar 0
        end
    | RO.nApp =>
        match lookup_succ b v with
        | [vf; va] => T.tApp (extract_v fuel b ρ vf) (extract_v fuel b ρ va)
        | _ => T.tVar 0
        end
    | RO.nInd ind => T.tInd ind
    | RO.nRoll ind ctor nparams nrecs =>
        let xs := lookup_succ b v in
        let ps := take nparams xs in
        let rs := drop nparams xs in
        T.tRoll ind ctor (map (extract_v fuel b ρ) ps) (map (extract_v fuel b ρ) rs)
    | RO.nCase ind nbrs =>
        match lookup_succ b v with
        | vscrut :: vC :: brs =>
            T.tCase ind (extract_v fuel b ρ vscrut) (extract_v fuel b ρ vC)
              (map (extract_v fuel b ρ) (take nbrs brs))
        | _ => T.tVar 0
        end
    | RO.nSubst _ _ =>
        (* Substitution evidence nodes are not terms. They should only appear
           under backlinks. *)
        T.tVar 0
    | RO.nBack =>
        match lookup_succ b v with
        | target :: sv :: args =>
            (* Backlink becomes a call to the synthesized fix binder for `target`. *)
            match ρ !! target with
            | Some k =>
                (* Argument vertices are stored as successors of `sv`. *)
                let arg_vs := lookup_succ b sv in
                apps (T.tVar k) (map (extract_v fuel b ρ) arg_vs)
            | None =>
                (* If this happens, the graph is not in the expected normal form:
                   we encountered a backlink without an enclosing fix binder. *)
                T.tVar 0
            end
        | _ => T.tVar 0
        end
    end.

  Definition extract (b : RO.builder) (root : nat) : T.tm :=
    extract_v (RO.b_next b + 1) b (∅ : fix_env) root.

  Definition extract_read_off (t : T.tm) : T.tm :=
    let '(root, b) := RO.read_off_raw t in
    extract b root.
End Extract.
