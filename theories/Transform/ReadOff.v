From Stdlib Require Import List Arith Lia Utf8.
From stdpp Require Import prelude gmap.

From Cyclic.Syntax Require Import Term.

Import ListNotations.

Set Default Proof Using "Type".

Module T := Term.Syntax.

(**
  Read-off compilation (stage 2: fix-free vertices + backlink+subst)

  This file implements a *fix-free* cyclic term-graph representation.

  Design constraints (per project plan):
  - no `tFix` nodes appear in the cyclic object (neither in terms nor types)
  - recursion is represented only by graph cycles/back-links
  - every back-link carries explicit substitution evidence as a dedicated
    `Subst` vertex

  Current deliverable:
  - a computational compiler from `T.tm` to a raw cyclic graph (as maps)

  Next deliverable (separate step):
  - package the result as a `Preproof.rooted_preproof` with vertex-based
    judgements and a rule relation.
*)

Section ReadOff.
  Inductive node : Type :=
  | nVar (x : nat)
  | nSort (i : nat)
  | nPi
  | nLam
  | nApp
  | nInd (ind : nat)
  | nRoll (ind ctor nparams nrecs : nat)
  | nCase (ind nbrs : nat)
  | nSubstNil (k : nat)
  | nSubstCons (k : nat)
  | nBack.

  (* For each de Bruijn index, either it is not a recursive variable (`None`)
     or it points to the cycle target vertex (`Some v`). *)
  Definition back_env : Type := list (option nat).

  Record builder : Type := {
    b_next : nat;
    b_label : gmap nat node;
    b_succ : gmap nat (list nat);
    (* If a vertex is used as a cycle target for a source `tFix A _`, record the
       compiled type vertex for `A` here. This is metadata for extraction. *)
    b_fix_ty : gmap nat nat;
  }.

  Definition empty_builder : builder :=
    {| b_next := 0; b_label := ∅; b_succ := ∅; b_fix_ty := ∅ |}.

  (* Decompose an application spine into head and arguments (left-associated). *)
  Fixpoint app_view (t : T.tm) : T.tm * list T.tm :=
    match t with
    | T.tApp t u =>
        let '(h, args) := app_view t in
        (h, args ++ [u])
    | _ => (t, [])
    end.

  (* Allocate a fresh vertex id. *)
  Definition fresh (b : builder) : nat * builder :=
    let v := b.(b_next) in
    (v,
      {| b_next := S v;
         b_label := b.(b_label);
         b_succ := b.(b_succ);
         b_fix_ty := b.(b_fix_ty) |}).

  (* Fill a vertex with a label and successor list. *)
  Definition put (v : nat) (lbl : node) (succs : list nat) (b : builder) : builder :=
    {| b_next := b.(b_next);
       b_label := <[v := lbl]> b.(b_label);
       b_succ := <[v := succs]> b.(b_succ);
       b_fix_ty := b.(b_fix_ty) |}.

  (* Record the type vertex for a cycle target. *)
  Definition put_fix_ty (v vA : nat) (b : builder) : builder :=
    {| b_next := b.(b_next);
       b_label := b.(b_label);
       b_succ := b.(b_succ);
       b_fix_ty := <[v := vA]> b.(b_fix_ty) |}.

  Fixpoint build_subst_chain (us : list nat) (sv_tail : nat) (b : builder)
    {struct us} : nat * builder :=
    match us with
    | [] => (sv_tail, b)
    | u :: us =>
        let '(sv_tail', b1) := build_subst_chain us sv_tail b in
        let '(sv_head, b2) := fresh b1 in
        (sv_head, put sv_head (nSubstCons 0) [u; sv_tail'] b2)
    end.

  Fixpoint compile_tm (fuel : nat) (ρ : back_env) (t : T.tm) (b : builder)
    {struct fuel} : nat * builder :=
    match fuel with
    | 0 =>
        let '(v, b1) := fresh b in
        (v, put v (nVar 0) [] b1)
    | S fuel' =>
        match t with
        | T.tVar x =>
            let '(v, b1) := fresh b in
            (v, put v (nVar x) [] b1)

        | T.tSort i =>
            let '(v, b1) := fresh b in
            (v, put v (nSort i) [] b1)

        | T.tPi A B =>
            let '(vA, b1) := compile_tm fuel' ρ A b in
            let '(vB, b2) := compile_tm fuel' (None :: ρ) B b1 in
            let '(v, b3) := fresh b2 in
            (v, put v nPi [vA; vB] b3)

        | T.tLam A t =>
            let '(vA, b1) := compile_tm fuel' ρ A b in
            let '(vt, b2) := compile_tm fuel' (None :: ρ) t b1 in
            let '(v, b3) := fresh b2 in
            (v, put v nLam [vA; vt] b3)

        | T.tApp t1 u1 =>
            (* Backlink detection uses the full spine. *)
            let '(h, args) := app_view t in
            match h with
            | T.tVar x =>
                match nth_error ρ x with
                 | Some (Some target) =>
                     (* Compile each argument as a vertex.

                        We use a fuel-decreasing list compilation so that the
                        i-th argument is compiled with the same fuel that
                        `Extract.subst_args` will later use to extract it.
                     *)
                     let '(v_args, b1) := compile_args fuel' ρ args b in
                    (* Build an explicit substitution evidence chain.

                       We represent substitutions as linked vertices:
                       - `sv_nil` has label `nSubstNil 0` and no successors.
                       - for each argument `u`, create a `nSubstCons 0` vertex
                         with successors `[u; sv_tail]`.

                       The head of the chain is the substitution vertex `sv`.
                    *)
                    let '(sv_nil, b2) := fresh b1 in
                    let b3 := put sv_nil (nSubstNil 0) [] b2 in
                    let '(sv, b4) := build_subst_chain v_args sv_nil b3 in
                    (* Allocate the backlink node `v` pointing to target and substitution. *)
                    let '(v, b5) := fresh b4 in
                    let b6 := put v nBack [target; sv] b5 in
                    (v, b6)
                | _ =>
                    let '(v1, b1) := compile_tm fuel' ρ t1 b in
                    let '(v2, b2) := compile_tm fuel' ρ u1 b1 in
                    let '(v, b3) := fresh b2 in
                    (v, put v nApp [v1; v2] b3)
                end
            | _ =>
                let '(v1, b1) := compile_tm fuel' ρ t1 b in
                let '(v2, b2) := compile_tm fuel' ρ u1 b1 in
                let '(v, b3) := fresh b2 in
                (v, put v nApp [v1; v2] b3)
            end

        | T.tFix A body =>
            (* Eliminate `tFix` by tying a cycle:
               - allocate the cycle target vertex `v`
               - record the compiled type vertex `vA` for extraction
               - compile the body in an environment where var 0 refers to `v`
               - write the body’s node label/succ into `v`

               NOTE: this assumes the body compilation can populate `v` by
               copying its root structure. We do this by compiling the body to a
               fresh root `vbody` and then aliasing `v` to that structure.

               This keeps the cyclic object fix-free.
            *)
            let '(v, b0) := fresh b in
            let '(vA, b1) := compile_tm fuel' ρ A b0 in
            let b1' := put_fix_ty v vA b1 in
            let '(vbody, b2) := compile_tm fuel' (Some v :: ρ) body b1' in
            (* Copy the body root shape into v (shallow alias). *)
            let lbl_body := default (nVar 0) (b2.(b_label) !! vbody) in
            let succ_body := default [] (b2.(b_succ) !! vbody) in
            (v, put v lbl_body succ_body b2)

        | T.tInd ind =>
            let '(v, b1) := fresh b in
            (v, put v (nInd ind) [] b1)

        | T.tRoll ind ctor params recs =>
            let '(vps, b1) := compile_list fuel' ρ params b in
            let '(vrs, b2) := compile_list fuel' ρ recs b1 in
            let '(v, b3) := fresh b2 in
            (v, put v (nRoll ind ctor (length vps) (length vrs)) (vps ++ vrs) b3)

        | T.tCase ind scrut C brs =>
            let '(vscrut, b1) := compile_tm fuel' ρ scrut b in
            let '(vC, b2) := compile_tm fuel' ρ C b1 in
            let '(vbrs, b3) := compile_list fuel' ρ brs b2 in
            let '(v, b4) := fresh b3 in
            (v, put v (nCase ind (length vbrs)) ([vscrut; vC] ++ vbrs) b4)
         end
     end

  with compile_list (fuel : nat) (ρ : back_env) (ts : list T.tm) (b : builder)
    {struct ts} : list nat * builder :=
    match ts with
    | [] => ([], b)
    | t :: ts =>
        let '(v, b1) := compile_tm fuel ρ t b in
        let '(vs, b2) := compile_list fuel ρ ts b1 in
        (v :: vs, b2)
    end.

  Fixpoint compile_args (fuel : nat) (ρ : back_env) (ts : list T.tm) (b : builder)
    {struct fuel} : list nat * builder :=
    match fuel with
    | 0 => ([], b)
    | S fuel' =>
        match ts with
        | [] => ([], b)
        | t :: ts =>
            let '(v, b1) := compile_tm fuel' ρ t b in
            let '(vs, b2) := compile_args fuel' ρ ts b1 in
            (v :: vs, b2)
        end
    end.


  Definition read_off_raw (t : T.tm) : nat * builder :=
    compile_tm (T.size t) [] t empty_builder.
End ReadOff.
