From Stdlib Require Import List Utf8.
From Cyclic.Syntax Require Import Term Examples ListNat.
From Cyclic.Transform Require Import Supercompile.
Import Term.Syntax.
Import ListNotations.

Set Default Proof Using "Type".

(**
  List Monad Laws

  The List monad on [List Nat] has:
    return x   = [x]                    (singleton)
    bind l f   = foldr (append ∘ f) nil l   (concatMap)
    fmap f l   = map f l

  We prove all three monad laws by supercompilation:
  both sides reduce to the same normal form under [vm_compute].

  This is the SC as an equational proof engine — it discovers the
  equalities by driving both sides and observing they normalise identically.
  Each [_killed] lemma is a theorem proved with zero human insight about
  the proof structure.
*)

Definition Σ := [Examples.Nat_sig; ListNat.List_sig].

(* ------------------------------------------------------------------ *)
(** * Contexts                                                          *)

Definition Γ_x   := [Examples.nat_ty].
Definition Γ_l   := [ListNat.list_ty].
Definition Γ_xf  := [Examples.nat_ty; tPi Examples.nat_ty ListNat.list_ty].
Definition Γ_lf  := [ListNat.list_ty; tPi Examples.nat_ty ListNat.list_ty].
Definition Γ_lfg := [ListNat.list_ty;
                     tPi Examples.nat_ty ListNat.list_ty;
                     tPi Examples.nat_ty ListNat.list_ty].

(* ------------------------------------------------------------------ *)
(** * Law 1: Left Identity   bind (return x) f = f x                  *)
(**                                                                    *)
(**   LHS: bind (cons x nil) f                                         *)
(**        = append (f x) (bind nil f)                                 *)
(**        = append (f x) nil                                           *)
(**        = f x                                                        *)
(**                                                                    *)
(**   Both sides SC to [f x] directly.                                 *)
(* ------------------------------------------------------------------ *)

(** LHS: bind (return x) f  where x = tVar 1, f = tVar 0 *)
Definition t_left_id_lhs : tm :=
  tApp (tApp ListNat.bind
              (tApp ListNat.return_list (tVar 1)))
       (tVar 0).

(** RHS: f x *)
Definition t_left_id_rhs : tm :=
  tApp (tVar 0) (tVar 1).

Definition r_left_id_lhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_xf
    t_left_id_lhs ListNat.list_ty.

Definition r_left_id_rhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_xf
    t_left_id_rhs ListNat.list_ty.

Theorem monad_left_identity :
  r_left_id_lhs = r_left_id_rhs.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Law 2: Right Identity   bind l return = l                        *)
(**                                                                    *)
(**   LHS: bind l (cons · nil)                                         *)
(**   After driving through l:                                          *)
(**     nil  → nil                                                     *)
(**     cons x xs → append [x] (bind xs return)                       *)
(**              = cons x (bind xs return)                             *)
(**   Backlink on xs: the residual is the identity function on l.      *)
(* ------------------------------------------------------------------ *)

Definition t_right_id_lhs : tm :=
  tApp (tApp ListNat.bind (tVar 0))
       ListNat.return_list.

Definition t_right_id_rhs : tm := tVar 0.

Definition r_right_id_lhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_right_id_lhs ListNat.list_ty.

Definition r_right_id_rhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_right_id_rhs ListNat.list_ty.

Theorem monad_right_identity :
  r_right_id_lhs = r_right_id_rhs.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Law 3: Associativity                                             *)
(**   bind (bind l f) g = bind l (λx. bind (f x) g)                   *)
(**                                                                    *)
(**   LHS: bind (bind l f) g                                           *)
(**   RHS: bind l (λx. bind (f x) g)                                   *)
(**                                                                    *)
(**   Context: l = tVar 2, f = tVar 1, g = tVar 0                     *)
(**                                                                    *)
(**   The SC drives both sides through l, then through f x, and        *)
(**   discovers they produce identical append-trees.                   *)
(**   This is the deepest of the three laws — it requires the SC to    *)
(**   commute two nested folds, equivalent to append associativity.    *)
(* ------------------------------------------------------------------ *)

(** LHS: bind (bind l f) g *)
Definition t_assoc_lhs : tm :=
  tApp (tApp ListNat.bind
              (tApp (tApp ListNat.bind (tVar 2)) (tVar 1)))
       (tVar 0).

(** RHS: bind l (λx. bind (f x) g) *)
Definition t_assoc_rhs : tm :=
  tApp (tApp ListNat.bind (tVar 2))
       (tLam Examples.nat_ty
              (tApp (tApp ListNat.bind (tApp (tVar 2) (tVar 0)))
                    (tVar 1))).

Definition r_assoc_lhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lfg
    t_assoc_lhs ListNat.list_ty.

Definition r_assoc_rhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lfg
    t_assoc_rhs ListNat.list_ty.

Theorem monad_associativity :
  r_assoc_lhs = r_assoc_rhs.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Functor laws (fmap = map)                                        *)
(**                                                                    *)
(**   fmap id l = l                    (identity)                      *)
(**   fmap (f ∘ g) l = fmap f (fmap g l)  (composition)               *)
(* ------------------------------------------------------------------ *)

(** Functor identity: map id l = l *)
Definition t_fmap_id : tm :=
  tApp (tApp ListNat.map (tLam Examples.nat_ty (tVar 0))) (tVar 0).

Definition r_fmap_id : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    t_fmap_id ListNat.list_ty.

Definition r_id_l : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_l
    (tVar 0) ListNat.list_ty.

Theorem functor_identity :
  r_fmap_id = r_id_l.
Proof. vm_compute. reflexivity. Qed.

(** Functor composition: map f (map g l) = map (f ∘ g) l *)
(**   Context: l = tVar 2, g = tVar 1, f = tVar 0 *)
Definition Γ_lfg_nat := [ListNat.list_ty; ListNat.nat2nat; ListNat.nat2nat].

Definition t_fmap_comp_lhs : tm :=
  tApp (tApp ListNat.map (tVar 2))
       (tApp (tApp ListNat.map (tVar 1)) (tVar 0)).

Definition t_fmap_comp_rhs : tm :=
  tApp (tApp ListNat.map
              (tLam Examples.nat_ty
                     (tApp (tVar 3) (tApp (tVar 2) (tVar 0)))))
       (tVar 0).

Definition r_fmap_comp_lhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lfg_nat
    t_fmap_comp_lhs ListNat.list_ty.

Definition r_fmap_comp_rhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lfg_nat
    t_fmap_comp_rhs ListNat.list_ty.

Theorem functor_composition :
  r_fmap_comp_lhs = r_fmap_comp_rhs.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Monad-functor coherence: fmap f l = bind l (return ∘ f)          *)
(**                                                                    *)
(**   map f l = bind l (λx. [f x])                                     *)
(**   Context: l = tVar 1, f = tVar 0                                  *)
(* ------------------------------------------------------------------ *)

Definition Γ_lf_nat := [ListNat.list_ty; ListNat.nat2nat].

Definition t_coherence_lhs : tm :=
  tApp (tApp ListNat.map (tVar 1)) (tVar 0).

Definition t_coherence_rhs : tm :=
  tApp (tApp ListNat.bind (tVar 0))
       (tLam Examples.nat_ty
              (tApp ListNat.return_list (tApp (tVar 2) (tVar 0)))).

Definition r_coherence_lhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lf_nat
    t_coherence_lhs ListNat.list_ty.

Definition r_coherence_rhs : option tm :=
  Supercompile.residualise_jTy_fp 6 200 600 Σ Γ_lf_nat
    t_coherence_rhs ListNat.list_ty.

Theorem monad_functor_coherence :
  r_coherence_lhs = r_coherence_rhs.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Summary                                                          *)
(**                                                                    *)
(**   All 5 laws proved by supercompilation alone:                     *)
(**                                                                    *)
(**   monad_left_identity    : bind (return x) f  = f x               *)
(**   monad_right_identity   : bind l return      = l                  *)
(**   monad_associativity    : bind (bind l f) g  = bind l (λx.bind (f x) g) *)
(**   functor_identity       : map id l            = l                 *)
(**   functor_composition    : map f (map g l)     = map (f∘g) l       *)
(**   monad_functor_coherence: map f l             = bind l (return∘f) *)
(**                                                                    *)
(**   Proof method: both sides SC to the same normal form.             *)
(**   The SC discovers the equalities by driving + cyclic backlinks.   *)
(**   No human-provided lemmas, no induction tactics, no rewrite hints. *)
(* ------------------------------------------------------------------ *)
