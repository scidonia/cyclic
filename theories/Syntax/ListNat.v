From Cyclic.Syntax Require Import StrictPos Term Examples.

From Stdlib Require Import List.

From Cyclic.Syntax Require Import StrictPos Term Examples.

Import ListNotations.
Import Term.Syntax.

Set Default Proof Using "Type".

Module ListNat.

  (** We assume [Nat] is inductive 0 (from [Syntax.Examples]).
      We define [List Nat] as inductive 1. *)

  Definition list_ty : tm := tInd 1 [].

  Definition List_sig : ind_sig tm := {|
    ind_params := [];
    ind_indices := [];
    ind_level := 0;
    ind_ctors := [
      {| ctor_param_tys := []; ctor_rec_args := []; ctor_indices := [] |};
      {| ctor_param_tys := [Examples.nat_ty]; ctor_rec_args := [[]]; ctor_indices := [] |}
    ]
  |}.

  Definition nil : tm := tRoll 1 0 [].
  Definition cons (x xs : tm) : tm := tRoll 1 1 [x; xs].

  (** A simple function type [Nat -> Nat]. *)
  Definition nat2nat : tm := tPi Examples.nat_ty Examples.nat_ty.

  (** map : (Nat -> Nat) -> List -> List *)
  Definition map_ty : tm := tPi nat2nat (tPi list_ty list_ty).

  Definition map_body : tm :=
    (* self : map_ty *)
    tLam nat2nat ( (* f : Nat -> Nat *)
      tLam list_ty ( (* l : List *)
        tCase 1 (tVar 0) list_ty
          [ nil;
            (* cons branch: \x:Nat. \xs:List. cons (f x) (map f xs) *)
            tLam Examples.nat_ty (
              tLam list_ty (
                cons
                  (tApp (tVar 3) (tVar 1))
                  (tApp (tApp (tVar 4) (tVar 3)) (tVar 0))
              ))
          ]
      )).

  Definition map : tm := tFix map_ty map_body.

  (** append : List -> List -> List *)
  Definition append_ty : tm := tPi list_ty (tPi list_ty list_ty).

  Definition append_body : tm :=
    (* self : append_ty *)
    tLam list_ty ( (* l1 *)
      tLam list_ty ( (* l2 *)
        tCase 1 (tVar 1) list_ty
          [ tVar 0; (* nil -> l2 *)
            (* cons branch: \x:Nat. \xs:List. cons x (append xs l2) *)
            tLam Examples.nat_ty (
              tLam list_ty (
                cons (tVar 1)
                  (tApp (tApp (tVar 4) (tVar 0)) (tVar 2))
              ))
          ]
      )).

  Definition append : tm := tFix append_ty append_body.

  (** take : Nat -> List -> List *)
  Definition take_ty : tm := tPi Examples.nat_ty (tPi list_ty list_ty).

  Definition take_body : tm :=
    (* self : take_ty *)
    tLam Examples.nat_ty ( (* n *)
      tLam list_ty ( (* l *)
        tCase 0 (tVar 1) list_ty
          [ nil;
            (* succ branch: \n'. case l of nil -> nil | cons x xs -> cons x (take n' xs) *)
            tLam Examples.nat_ty (
              tCase 1 (tVar 1) list_ty
                [ nil;
                  tLam Examples.nat_ty (
                    tLam list_ty (
                      cons (tVar 1)
                        (tApp (tApp (tVar 5) (tVar 2)) (tVar 0))
                    ))
                ])
          ]
      )).

  Definition take : tm := tFix take_ty take_body.

  (** drop : Nat -> List -> List *)
  Definition drop_ty : tm := tPi Examples.nat_ty (tPi list_ty list_ty).

  Definition drop_body : tm :=
    (* self : drop_ty *)
    tLam Examples.nat_ty ( (* n *)
      tLam list_ty ( (* l *)
        tCase 0 (tVar 1) list_ty
          [ tVar 0;
            (* succ branch: \n'. case l of nil -> nil | cons x xs -> drop n' xs *)
            tLam Examples.nat_ty (
              tCase 1 (tVar 1) list_ty
                [ nil;
                  tLam Examples.nat_ty (
                    tLam list_ty (
                      tApp (tApp (tVar 5) (tVar 2)) (tVar 0)
                    ))
                ])
          ]
      )).

  Definition drop : tm := tFix drop_ty drop_body.

  (** length : List -> Nat *)
  Definition length_ty : tm := tPi list_ty Examples.nat_ty.

  Definition length_body : tm :=
    (* self : length_ty *)
    tLam list_ty (
      tCase 1 (tVar 0) Examples.nat_ty
        [ Examples.zero;
          (* cons branch: \x:Nat. \xs:List. succ (length xs) *)
          tLam Examples.nat_ty (
            tLam list_ty (
              Examples.succ (tApp (tVar 3) (tVar 0))
            ))
        ]
    ).

  Definition length : tm := tFix length_ty length_body.

  (** Convenience: list notation in the object language. *)
  Fixpoint list_lit (xs : list tm) : tm :=
    match xs with
    | [] => nil
    | x :: xs => cons x (list_lit xs)
    end.

End ListNat.
