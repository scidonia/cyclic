From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile LemmaEnv OmegaRule.
Import Term.Syntax.
Import ListNotations.
Set Default Proof Using "Type".

(**
  Dependent Type Benchmarks: Vec Index Normalisation

  Σ = [Nat (I=0), Vec nat n (I=1)]
  Vec at I=1 with two constructors:
    vnil  : Vec nat 0        (tRoll 1 0 [])
    vcons : ∀ n. nat → Vec nat n → Vec nat (S n)  (tRoll 1 1 [n; a; v])
*)

(** Σ with just Nat and Vec — no List, no Maybe, etc. *)
Definition Σ_vec : Typing.Typing.env := [Examples.Nat_sig; Examples.Vec_sig].

(** Vec constructor helpers at I=1 *)
Definition vec_ty (n : tm) : tm := tInd 1 [Examples.nat_ty; n].
Definition v_nil    : tm := tRoll 1 0 [].
Definition v_cons (n a v : tm) : tm := tRoll 1 1 [n; a; v].

(* ------------------------------------------------------------------ *)
(** 1. Vec length extracts the index                                  *)
(* ------------------------------------------------------------------ *)

(** vlen : ∀ n. Vec n → Nat *)
Definition vlen : tm :=
  tLam Examples.nat_ty (  (* tVar 0 = n *)
    tLam (vec_ty (tVar 0)) (  (* tVar 0 = v, tVar 1 = n *)
      tCase 1 (tVar 0) Examples.nat_ty [
        Examples.zero ;   (* vnil → 0 *)
        (* vcons: binds n', a, v_tail → succ n' *)
        tLam Examples.nat_ty (
          tLam Examples.nat_ty (
            tLam (vec_ty (tVar 0))
                 (Examples.succ (tVar 2))  (* tVar 2 = n' *)
          ))
      ])).

(** vmap : ∀ n. (Nat → Nat) → Vec n → Vec n *)
Definition vmap : tm :=
  tLam Examples.nat_ty (  (* tVar 0 = n *)
    tLam (tPi Examples.nat_ty Examples.nat_ty) (  (* tVar 0 = f, tVar 1 = n *)
      tLam (vec_ty (tVar 1)) (  (* tVar 0 = v, tVar 1 = f, tVar 2 = n *)
        tCase 1 (tVar 0) (vec_ty (tVar 2)) [
          v_nil ;  (* vnil → vnil *)
          tLam Examples.nat_ty (  (* n' *)
            tLam Examples.nat_ty (  (* a *)
              tLam (vec_ty (tVar 0))
                   (v_cons (Examples.succ (tVar 2))
                           (tApp (tVar 5) (tVar 1))
                           (tApp (tVar 4) (tVar 0)))
          ))
        ]))).

(* ------------------------------------------------------------------ *)
(** * Theorems                                                        *)
(* ------------------------------------------------------------------ *)

(** Theorem 1: length of vmap equals length of original — both reduce to n *)
Definition t_vlen_vmap : tm :=
  tApp vlen (tVar 2) (tApp vmap (tVar 2) (tVar 1) (tVar 0)).
  (* arguments: n, f, v *)

Definition t_vlen_id : tm :=
  tApp vlen (tVar 2) (tVar 0).

Definition Γ_v3 : Typing.Typing.ctx :=
  [vec_ty (tVar 2); tPi Examples.nat_ty Examples.nat_ty; Examples.nat_ty].

(* Can't express Γ_v3 like this — it depends on tVar 2... 

   Let me use a concrete context: [n:Nat, f:Nat->Nat, v:Vec n]
   But the type of v depends on n, which depends on the context order.
   For the SC, [Vec n; Nat→Nat; Nat] where indices are:
     tVar 0 = n, tVar 1 = f, tVar 2 = v
   But Vec n needs n to be in the context... tVar 0 is n.
   Actually: [Nat; Nat→Nat; Vec n] where:
     tVar 0 = n, tVar 1 = f, tVar 2 = v
   And vec_ty n needs tVar 0.
   So: Γ = [nat_ty; nat2nat; tInd 1 [nat_ty; tVar 0]]
   But tVar 0 in the context refers to nat_ty...
   
   Let me just use concrete types for the test: *)
*)

(** Concrete test: vlen (vmap 2 succ v) = 2 *)
Definition v_example : tm :=
  v_cons (Examples.succ Examples.zero)  (* n'=1 *)
         Examples.zero                   (* a=0 *)
         (v_cons Examples.zero           (* n'=0 *)
                  (Examples.succ Examples.zero)  (* a=1 *)
                  v_nil).

Definition t_concrete : tm :=
  tApp vlen (Examples.succ (Examples.succ Examples.zero))
       (tApp vmap (Examples.succ (Examples.succ Examples.zero))
           Examples.succ_fn v_example).

Lemma concrete_vlen_vmap :
  Supercompile.residualise_jTy 80 200 Σ_vec [] t_concrete Examples.nat_ty
  = Some (Examples.succ (Examples.succ Examples.zero)).
Proof. vm_compute. reflexivity. Qed.

(** Abstract: vlen (vmap n f v) = n (the index, regardless of f and v)
    This is the core dependent-type property.

    Γ = [n : Nat, f : Nat→Nat, v : Vec n]
    n = tVar 2, f = tVar 1, v = tVar 0

    The Vec type references n at a different position: tInd 1 [nat_ty; tVar 2]
    because tVar 2 = n in the enclosing context. *)
Lemma vlen_vmap_equals_n_forall :
  forall fuel fuel_res,
  Supercompile.residualise_jTy fuel fuel_res Σ_vec
    [Examples.nat_ty;
     tPi Examples.nat_ty Examples.nat_ty;
     tInd 1 [Examples.nat_ty; tVar 2]]
    (tApp
       (tApp vlen (tVar 2))
       (tApp vmap (tVar 2) (tVar 1) (tVar 0)))
    Examples.nat_ty
  = Supercompile.residualise_jTy fuel fuel_res Σ_vec
    [Examples.nat_ty;
     tPi Examples.nat_ty Examples.nat_ty;
     tInd 1 [Examples.nat_ty; tVar 2]]
    (tVar 2)
    Examples.nat_ty.
Proof.
  intros. vm_compute. reflexivity.
Qed.

(** For any fuel, vlen (vmap n f v) = vlen v = n.
    The SC normalises the dependent index identically.
    Even though v depends on n in its TYPE, the SC eliminates the
    dependency through driving. *)

