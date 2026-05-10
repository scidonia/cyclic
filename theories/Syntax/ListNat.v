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

  (** sum : List -> Nat  (sum of elements) *)
  Definition sum_ty : tm := tPi list_ty Examples.nat_ty.

  Definition sum_body : tm :=
    (* tVar 0 = self : sum_ty *)
    tLam list_ty ( (* tVar 0 = l, tVar 1 = self *)
      tCase 1 (tVar 0) Examples.nat_ty
        [ Examples.zero;
          (* cons branch: \x:Nat. \xs:List. plus x (sum xs) *)
          tLam Examples.nat_ty (   (* tVar 0 = x, tVar 1 = xs... wait *)
            (* After tCase match on tVar 0 (l), cons branch binds x then xs *)
            tLam list_ty (         (* tVar 0 = xs, tVar 1 = x, tVar 2 = l(orig), tVar 3 = self *)
              tApp (tApp Examples.plusL (tVar 1))
                   (tApp (tVar 3) (tVar 0))
            ))
        ]
    ).

  Definition sum : tm := tFix sum_ty sum_body.

  (** rev_acc : List -> List -> List  (tail-recursive reverse helper)
      rev_acc l acc = reverse l ++ acc *)
  Definition rev_acc_ty : tm := tPi list_ty (tPi list_ty list_ty).

  Definition rev_acc_body : tm :=
    (* tVar 0 = self : rev_acc_ty *)
    tLam list_ty (   (* tVar 0 = l, tVar 1 = self *)
      tLam list_ty ( (* tVar 0 = acc, tVar 1 = l, tVar 2 = self *)
        tCase 1 (tVar 1) list_ty
          [ tVar 0; (* nil -> acc *)
            (* cons branch: \x:Nat. \xs:List.
               tVar 0 = xs, tVar 1 = x, tVar 2 = acc, tVar 3 = l, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                tApp (tApp (tVar 4) (tVar 0))
                     (cons (tVar 1) (tVar 2))
              ))
          ]
      )).

  Definition rev_acc : tm := tFix rev_acc_ty rev_acc_body.

  (** reverse : List -> List *)
  Definition reverse_ty : tm := tPi list_ty list_ty.

  (** reverse l = rev_acc l nil *)
  Definition reverse : tm :=
    tLam list_ty (tApp (tApp rev_acc (tVar 0)) nil).

  (** ------------------------------------------------------------------ *)
  (** List monad                                                          *)

  (** return_list : Nat -> List  (singleton) *)
  Definition return_list : tm :=
    tLam Examples.nat_ty (cons (tVar 0) nil).

  (** concat : List (List Nat) -> List Nat  (flatten one level)
      We encode List (List Nat) as List Nat lists passed as List;
      since our type system is simply-typed here, concat : List -> List
      where each element is itself a List encoded as a Nat — but that
      doesn't work cleanly.

      Instead we encode the List monad directly via [concatMap]:
        bind l f = concatMap f l = foldr (append ∘ f) nil l

      [concat] itself needs List-of-Lists, which requires a second
      inductive.  We sidestep this by defining [bind] directly. *)

  (** bind : List -> (Nat -> List) -> List
      bind l f = foldr (\x acc. append (f x) acc) nil l *)
  Definition bind_ty : tm :=
    tPi list_ty (tPi (tPi Examples.nat_ty list_ty) list_ty).

  Definition bind_body : tm :=
    (* tVar 0 = self : bind_ty *)
    tLam list_ty (             (* tVar 0 = l,  tVar 1 = self *)
      tLam (tPi Examples.nat_ty list_ty) ( (* tVar 0 = f, tVar 1 = l, tVar 2 = self *)
        tCase 1 (tVar 1) list_ty
          [ nil ;              (* nil   → nil *)
            (* cons branch: tVar 0 = xs, tVar 1 = x, tVar 2 = f, tVar 3 = l, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                tApp (tApp append (tApp (tVar 2) (tVar 1)))
                     (tApp (tApp (tVar 4) (tVar 0)) (tVar 2))
              ))
          ]
      )).

  Definition bind : tm := tFix bind_ty bind_body.

  (** join : List (List) -> List  — flatten via bind id
      join l = bind l (fun x => x)
      Since our lists are List Nat, join doesn't type directly, but
      the monad law for join is expressible via bind. *)

  (** fmap = map (already defined above as [map]) *)

  (** ------------------------------------------------------------------ *)
  (** Maybe monad (Option)                                               *)
  (**                                                                    *)
  (**   We encode Maybe Nat as:                                          *)
  (**     nothing = tRoll 2 0 []           (constructor 0, no args)     *)
  (**     just x  = tRoll 2 1 [x]          (constructor 1, one arg)     *)
  (**                                                                    *)
  (**   This requires a third inductive in the signature.               *)

  Definition Maybe_sig : ind_sig tm := {|
    ind_params := [];
    ind_indices := [];
    ind_level := 0;
    ind_ctors := [
      {| ctor_param_tys := []; ctor_rec_args := []; ctor_indices := [] |};   (* nothing *)
      {| ctor_param_tys := [Examples.nat_ty]; ctor_rec_args := []; ctor_indices := [] |}  (* just *)
    ]
  |}.

  Definition maybe_ty   : tm := tInd 2 [].
  Definition nothing    : tm := tRoll 2 0 [].
  Definition just (x : tm) : tm := tRoll 2 1 [x].

  (** return_maybe : Nat -> Maybe *)
  Definition return_maybe : tm :=
    tLam Examples.nat_ty (just (tVar 0)).

  (** bind_maybe : Maybe -> (Nat -> Maybe) -> Maybe *)
  Definition bind_maybe_ty : tm :=
    tPi maybe_ty (tPi (tPi Examples.nat_ty maybe_ty) maybe_ty).

  Definition bind_maybe : tm :=
    tLam maybe_ty (             (* tVar 0 = m *)
      tLam (tPi Examples.nat_ty maybe_ty) ( (* tVar 0 = f, tVar 1 = m *)
        tCase 2 (tVar 1) maybe_ty
          [ nothing ;           (* nothing → nothing *)
            (* just branch: tVar 0 = x *)
            tLam Examples.nat_ty (
              tApp (tVar 1) (tVar 0)   (* f x *)
            )
          ]
      )).

  (** leb : Nat -> Nat -> Bool (less-than-or-equal, encoded as Nat: 0=false, succ=true) *)
  (** We encode Bool as Nat: zero = false, succ zero = true. *)
  Definition bool_ty : tm := tInd 0 [].  (* reuse Nat as Bool — 0=false, S _=true *)
  Definition bool_false : tm := Examples.zero.
  Definition bool_true  : tm := Examples.succ Examples.zero.

  (** leb : Nat -> Nat -> Nat (0=false, 1=true)
      leb 0 _     = true
      leb (S m) 0 = false
      leb (S m) (S n) = leb m n *)
  Definition leb_ty : tm := tPi Examples.nat_ty (tPi Examples.nat_ty Examples.nat_ty).

  Definition leb_body : tm :=
    (* tVar 0 = self *)
    tLam Examples.nat_ty ( (* tVar 0 = m, tVar 1 = self *)
      tLam Examples.nat_ty ( (* tVar 0 = n, tVar 1 = m, tVar 2 = self *)
        tCase 0 (tVar 1) Examples.nat_ty
          [ bool_true ;  (* m = zero → true *)
            (* succ branch: m = S m', tVar 0 = m' *)
            tLam Examples.nat_ty ( (* tVar 0 = m', tVar 1 = n, tVar 2 = m, tVar 3 = self *)
              tCase 0 (tVar 1) Examples.nat_ty
                [ bool_false ; (* n = zero → false *)
                  (* succ branch: n = S n', tVar 0 = n' *)
                  tLam Examples.nat_ty (
                    tApp (tApp (tVar 4) (tVar 1)) (tVar 0)
                  )
                ]
            )
          ]
      )).

  Definition leb : tm := tFix leb_ty leb_body.

  (** insert : Nat -> List -> List  (insert into sorted list) *)
  Definition insert_ty : tm := tPi Examples.nat_ty (tPi list_ty list_ty).

  Definition insert_body : tm :=
    (* tVar 0 = self *)
    tLam Examples.nat_ty ( (* tVar 0 = x, tVar 1 = self *)
      tLam list_ty ( (* tVar 0 = l, tVar 1 = x, tVar 2 = self *)
        tCase 1 (tVar 0) list_ty
          [ cons (tVar 1) nil ; (* nil → [x] *)
            (* cons branch: tVar 0 = ys, tVar 1 = y, tVar 2 = l, tVar 3 = x, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                tCase 0 (tApp (tApp leb (tVar 3)) (tVar 1)) list_ty
                  [ (* leb x y = false, i.e. x > y: cons y (insert x ys) *)
                    cons (tVar 1) (tApp (tApp (tVar 4) (tVar 3)) (tVar 0)) ;
                    (* leb x y = true (succ branch), i.e. x ≤ y: cons x (cons y ys) *)
                    tLam Examples.nat_ty (
                      cons (tVar 4) (cons (tVar 2) (tVar 1))
                    )
                  ]
              ))
          ]
      )).

  Definition insert : tm := tFix insert_ty insert_body.

  (** sort : List -> List  (insertion sort) *)
  Definition sort_ty : tm := tPi list_ty list_ty.

  Definition sort_body : tm :=
    (* tVar 0 = self *)
    tLam list_ty ( (* tVar 0 = l, tVar 1 = self *)
      tCase 1 (tVar 0) list_ty
        [ nil ;
          (* cons branch: tVar 0 = xs, tVar 1 = x, tVar 2 = l, tVar 3 = self *)
          tLam Examples.nat_ty (
            tLam list_ty (
              tApp (tApp insert (tVar 1)) (tApp (tVar 3) (tVar 0))
            ))
        ]).

  Definition sort : tm := tFix sort_ty sort_body.

  (** member : Nat -> List -> Bool (0=false, succ=true) *)
  Definition member_ty : tm := tPi Examples.nat_ty (tPi list_ty Examples.nat_ty).

  Definition member_body : tm :=
    (* tVar 0 = self *)
    tLam Examples.nat_ty ( (* tVar 0 = x, tVar 1 = self *)
      tLam list_ty ( (* tVar 0 = l, tVar 1 = x, tVar 2 = self *)
        tCase 1 (tVar 0) Examples.nat_ty
          [ bool_false ;
            (* cons branch: tVar 0 = xs, tVar 1 = y, tVar 2 = l, tVar 3 = x, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                (* if x = y then true else member x xs *)
                (* encode eq as: leb x y && leb y x *)
                tCase 0 (tApp (tApp leb (tVar 3)) (tVar 1)) Examples.nat_ty
                  [ (* leb x y = false → not equal → recurse *)
                    tApp (tApp (tVar 4) (tVar 3)) (tVar 0) ;
                    tLam Examples.nat_ty (
                      tCase 0 (tApp (tApp leb (tVar 2)) (tVar 4)) Examples.nat_ty
                        [ tApp (tApp (tVar 5) (tVar 4)) (tVar 1) ;
                          tLam Examples.nat_ty bool_true
                        ]
                    )
                  ]
              ))
          ]
      )).

  Definition member : tm := tFix member_ty member_body.

  (** sorted : List -> Bool  (checks if list is sorted ascending) *)
  Definition sorted_ty : tm := tPi list_ty Examples.nat_ty.

  Definition sorted_body : tm :=
    (* tVar 0 = self *)
    tLam list_ty ( (* tVar 0 = l, tVar 1 = self *)
      tCase 1 (tVar 0) Examples.nat_ty
        [ bool_true ;
          (* cons branch: tVar 0 = xs, tVar 1 = x *)
          tLam Examples.nat_ty (
            tLam list_ty (
              tCase 1 (tVar 0) Examples.nat_ty
                [ bool_true ; (* xs = nil → sorted *)
                  (* xs = cons y ys: tVar 0 = ys, tVar 1 = y *)
                  tLam Examples.nat_ty (
                    tLam list_ty (
                      (* x ≤ y && sorted (cons y ys) *)
                      tCase 0 (tApp (tApp leb (tVar 3)) (tVar 1)) Examples.nat_ty
                        [ bool_false ;
                          tLam Examples.nat_ty (
                            tApp (tVar 6) (cons (tVar 2) (tVar 1))
                          )
                        ]
                    ))
                ]))
        ]).

  Definition sorted : tm := tFix sorted_ty sorted_body.

  (** ------------------------------------------------------------------ *)
  (** Predicates on Nat: oddp, evenp, filter, any, all                   *)

  (** oddp : Nat -> Bool  (oddp 0 = false, oddp (S 0) = true, oddp (S(S n)) = oddp n) *)
  Definition oddp_ty : tm := tPi Examples.nat_ty Examples.nat_ty.
  Definition oddp : tm :=
    tFix oddp_ty (
      (* tVar 0 = self *)
      tLam Examples.nat_ty ( (* tVar 0 = n, tVar 1 = self *)
        tCase 0 (tVar 0) Examples.nat_ty
          [ bool_false ;            (* 0 → false *)
            tLam Examples.nat_ty (  (* S n', tVar 0 = n' *)
              tCase 0 (tVar 0) Examples.nat_ty
                [ bool_true ;        (* S 0 → true *)
                  tLam Examples.nat_ty (  (* S (S n''), tVar 0 = n'' *)
                    tApp (tVar 3) (tVar 0)  (* oddp n'' *)
                  )
                ]
            )
          ]
      )).

  (** evenp : Nat -> Bool *)
  Definition evenp_ty : tm := tPi Examples.nat_ty Examples.nat_ty.
  Definition evenp : tm :=
    tFix evenp_ty (
      (* tVar 0 = self *)
      tLam Examples.nat_ty ( (* tVar 0 = n, tVar 1 = self *)
        tCase 0 (tVar 0) Examples.nat_ty
          [ bool_true ;             (* 0 → true *)
            tLam Examples.nat_ty (  (* S n', tVar 0 = n' *)
              tCase 0 (tVar 0) Examples.nat_ty
                [ bool_false ;       (* S 0 → false *)
                  tLam Examples.nat_ty (  (* S (S n''), tVar 0 = n'' *)
                    tApp (tVar 3) (tVar 0)  (* evenp n'' *)
                  )
                ]
            )
          ]
      )).

  (** filter : (Nat -> Bool) -> List -> List *)
  Definition filter_ty : tm :=
    tPi (tPi Examples.nat_ty Examples.nat_ty) (tPi list_ty list_ty).

  Definition filter_body : tm :=
    (* tVar 0 = self *)
    tLam (tPi Examples.nat_ty Examples.nat_ty) ( (* tVar 0 = p, tVar 1 = self *)
      tLam list_ty ( (* tVar 0 = l, tVar 1 = p, tVar 2 = self *)
        tCase 1 (tVar 0) list_ty
          [ nil ;                  (* nil → nil *)
            (* cons branch: tVar 0 = xs, tVar 1 = x, tVar 2 = p, tVar 3 = l, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                tCase 0 (tApp (tVar 2) (tVar 1)) list_ty
                  [ (* p x = false → filter p xs *)
                    tApp (tApp (tVar 4) (tVar 2)) (tVar 0) ;
                    (* p x = true → cons x (filter p xs) *)
                    tLam Examples.nat_ty (
                      cons (tVar 2) (tApp (tApp (tVar 5) (tVar 3)) (tVar 1))
                    )
                  ]
              ))
          ]
      )).

  Definition filter : tm := tFix filter_ty filter_body.

  (** any : (Nat -> Bool) -> List -> Bool *)
  Definition any_ty : tm :=
    tPi (tPi Examples.nat_ty Examples.nat_ty) (tPi list_ty Examples.nat_ty).

  Definition any_body : tm :=
    (* tVar 0 = self *)
    tLam (tPi Examples.nat_ty Examples.nat_ty) ( (* tVar 0 = p, tVar 1 = self *)
      tLam list_ty ( (* tVar 0 = l, tVar 1 = p, tVar 2 = self *)
        tCase 1 (tVar 0) Examples.nat_ty
          [ bool_false ;           (* nil → false *)
            (* cons branch: tVar 0 = xs, tVar 1 = x, tVar 2 = p, tVar 3 = l, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                tCase 0 (tApp (tVar 2) (tVar 1)) Examples.nat_ty
                  [ (* p x = false → any p xs *)
                    tApp (tApp (tVar 4) (tVar 2)) (tVar 0) ;
                    (* p x = true → true *)
                    tLam Examples.nat_ty bool_true
                  ]
              ))
          ]
      )).

  Definition any : tm := tFix any_ty any_body.

  (** all : (Nat -> Bool) -> List -> Bool *)
  Definition all_ty : tm :=
    tPi (tPi Examples.nat_ty Examples.nat_ty) (tPi list_ty Examples.nat_ty).

  Definition all_body : tm :=
    (* tVar 0 = self *)
    tLam (tPi Examples.nat_ty Examples.nat_ty) ( (* tVar 0 = p, tVar 1 = self *)
      tLam list_ty ( (* tVar 0 = l, tVar 1 = p, tVar 2 = self *)
        tCase 1 (tVar 0) Examples.nat_ty
          [ bool_true ;            (* nil → true *)
            (* cons branch: tVar 0 = xs, tVar 1 = x, tVar 2 = p, tVar 3 = l, tVar 4 = self *)
            tLam Examples.nat_ty (
              tLam list_ty (
                tCase 0 (tApp (tVar 2) (tVar 1)) Examples.nat_ty
                  [ (* p x = false → false *)
                    bool_false ;
                    (* p x = true → all p xs *)
                    tLam Examples.nat_ty (
                      tApp (tApp (tVar 5) (tVar 3)) (tVar 1)
                    )
                  ]
              ))
          ]
      )).

  Definition all : tm := tFix all_ty all_body.

  (** map_append_fusion:
      map f (append l1 l2) = append (map f l1) (map f l2)
      Both sides should SC to the same normal form. *)

  (** ------------------------------------------------------------------ *)
  (** Gradual Cast Benchmark                                             *)
  (**                                                                    *)
  (**   Value ::= v_nat(n) | v_dyn(v) | v_wrong   (I=4)                 *)
  (**   Expr  ::= const(n) | plus(e1,e2) | cast_dyn(e) | uncast_nat(e)  *)
  (**   eval  : Expr → Value                                             *)

  Definition Value_sig : ind_sig tm := {|
    ind_params := [];
    ind_indices := [];
    ind_level := 0;
    ind_ctors := [
      {| ctor_param_tys := [Examples.nat_ty];  ctor_rec_args := [];  ctor_indices := [] |};  (* v_nat *)
      {| ctor_param_tys := [];  ctor_rec_args := [[]];  ctor_indices := [] |};              (* v_dyn *)
      {| ctor_param_tys := [];  ctor_rec_args := [];  ctor_indices := [] |}                 (* v_wrong *)
    ]
  |}.

  Definition value_ty : tm := tInd 5 [].
  Definition v_nat (n : tm) : tm := tRoll 5 0 [n].
  Definition v_dyn (v : tm) : tm := tRoll 5 1 [v].
  Definition v_wrong : tm := tRoll 5 2 [].

  Definition Expr_sig_val : ind_sig tm := {|
    ind_params := [];
    ind_indices := [];
    ind_level := 0;
    ind_ctors := [
      {| ctor_param_tys := [Examples.nat_ty]; ctor_rec_args := [];  ctor_indices := [] |};  (* const(n) *)
      {| ctor_param_tys := []; ctor_rec_args := [[]; []];           ctor_indices := [] |};  (* plus(e1,e2) *)
      {| ctor_param_tys := []; ctor_rec_args := [[]];               ctor_indices := [] |};  (* cast_dyn(e) *)
      {| ctor_param_tys := []; ctor_rec_args := [[]];               ctor_indices := [] |}   (* uncast_nat(e) *)
    ]
  |}.

  Definition expr_g_ty : tm := tInd 4 [].
  Definition g_const (n : tm)    : tm := tRoll 4 0 [n].
  Definition g_plus (e1 e2 : tm) : tm := tRoll 4 1 [e1; e2].
  Definition g_cast_dyn (e : tm)  : tm := tRoll 4 2 [e].
  Definition g_uncast_nat (e : tm) : tm := tRoll 4 3 [e].

  (** gradual_eval : Expr → Value *)
  Definition gradual_eval : tm :=
    tFix (tPi expr_g_ty value_ty) (
      (* tVar 0 = self *)
      tLam expr_g_ty (
        tCase 4 (tVar 0) value_ty [
          (* const n → v_nat n *)
          tLam Examples.nat_ty (v_nat (tVar 0)) ;
          (* plus e1 e2 *)
          tLam expr_g_ty (
            tLam expr_g_ty (
              tCase 5 (tApp (tVar 3) (tVar 1)) value_ty [
                tLam Examples.nat_ty (
                  tCase 5 (tApp (tVar 3) (tVar 0)) value_ty [
                    tLam Examples.nat_ty (v_nat (tApp (tApp Examples.plusL (tVar 1)) (tVar 0))) ;
                    tLam value_ty v_wrong ;
                    v_wrong ]) ;
                tLam value_ty v_wrong ;
                v_wrong ])) ;
          (* cast_dyn e *)
          tLam expr_g_ty (
            tCase 5 (tApp (tVar 1) (tVar 0)) value_ty [
              tLam Examples.nat_ty (v_dyn (v_nat (tVar 0))) ;
              tLam value_ty v_wrong ;
              v_wrong ]) ;
          (* uncast_nat e *)
          tLam expr_g_ty (
            tCase 5 (tApp (tVar 1) (tVar 0)) value_ty [
              v_wrong ;
              tLam value_ty (
                tCase 5 (tVar 0) value_ty [
                  tLam Examples.nat_ty (v_nat (tVar 0)) ;
                  tLam value_ty v_wrong ;
                  v_wrong ]) ;
              v_wrong ])
        ])).

  (** ------------------------------------------------------------------ *)
  (** Compiler Correctness Benchmark                                     *)
  (**                                                                    *)
  (**   expr ::= const(n) | add(e1, e2)   (I=3, inductive 3)           *)
  (**   compile : Expr → Code → Code      (Code = List Nat)             *)
  (**   exec    : Code → Stack → Stack    (Stack = List Nat)            *)
  (**   eval    : Expr → Nat                                           *)
  (**                                                                    *)
  (**   Code encoding: 0 = ADD, nonzero = PUSH(v)                       *)
  (**   Restriction: cannot push 0 (all evaluated values are positive)   *)

  Definition Expr_sig : ind_sig tm := {|
    ind_params := [];
    ind_indices := [];
    ind_level := 0;
    ind_ctors := [
      {| ctor_param_tys := [Examples.nat_ty]; ctor_rec_args := []; ctor_indices := [] |};  (* const(n) *)
      {| ctor_param_tys := []; ctor_rec_args := [[]; []]; ctor_indices := [] |}            (* add(e1,e2) *)
    ]
  |}.

  Definition expr_ty : tm := tInd 3 [].
  Definition expr_const (n : tm) : tm := tRoll 3 0 [n].
  Definition expr_add (e1 e2 : tm) : tm := tRoll 3 1 [e1; e2].

  (** compile : Expr -> List -> List *)
  Definition compile_ty : tm := tPi expr_ty (tPi list_ty list_ty).

  Definition compile : tm :=
    tFix compile_ty (
      (* tVar 0 = self *)
      tLam expr_ty (        (* tVar 0 = e, tVar 1 = self *)
        tLam list_ty (       (* tVar 0 = code, tVar 1 = e, tVar 2 = self *)
          tCase 3 (tVar 1) list_ty [
            (* const(n): push n *)
            tLam Examples.nat_ty ( (* tVar 0 = n, tVar 1 = code, tVar 2 = e, tVar 3 = self *)
              cons (tVar 0) (tVar 1))
            ;
            (* add(e1, e2): compile e2 then e1 then ADD *)
            tLam expr_ty (          (* tVar 0 = e1 *)
              tLam expr_ty (         (* tVar 0 = e2, tVar 1 = e1, tVar 2 = code, tVar 3 = e, tVar 4 = self *)
                tApp (tApp (tVar 4) (tVar 0))
                     (tApp (tApp (tVar 4) (tVar 1))
                            (cons Examples.zero (tVar 2)))
              ))
          ]))).

  (** eval : Expr -> Nat *)
  Definition eval_ty : tm := tPi expr_ty Examples.nat_ty.

  Definition eval : tm :=
    tFix eval_ty (
      (* tVar 0 = self *)
      tLam expr_ty (        (* tVar 0 = e, tVar 1 = self *)
        tCase 3 (tVar 0) Examples.nat_ty [
          tLam Examples.nat_ty tVar 0;   (* const(n) → n *)
          tLam expr_ty (                    (* tVar 0 = e1 *)
            tLam expr_ty (                   (* tVar 0 = e2, tVar 1 = e1, tVar 2 = e, tVar 3 = self *)
              tApp (tApp Examples.plus
                         (tApp (tVar 3) (tVar 1)))
                   (tApp (tVar 3) (tVar 0))
            ))
        ])).

  (** exec : List -> List -> List *)
  Definition exec_ty : tm := tPi list_ty (tPi list_ty list_ty).

  Definition exec : tm :=
    tFix exec_ty (
      (* tVar 0 = self *)
      tLam list_ty (        (* tVar 0 = code, tVar 1 = self *)
        tLam list_ty (       (* tVar 0 = stack, tVar 1 = code, tVar 2 = self *)
          tCase 1 (tVar 1) list_ty [
            tVar 0 ;  (* nil → stack *)
            tLam Examples.nat_ty (   (* tVar 0 = code_tail, tVar 1 = head, tVar 2 = stack, tVar 3 = code, tVar 4 = self *)
              tLam list_ty (          (* ditto, after second cons binding *)
                tCase 0 (tVar 1) list_ty [
                  (* head = 0 → ADD *)
                  tCase 1 (tVar 2) list_ty [
                    tVar 2 ;   (* stack=nil → return stack (safety) *)
                    tLam Examples.nat_ty ( (* a *)
                      tLam list_ty (       (* rest1 *)
                        tCase 1 (tVar 0) list_ty [
                          tVar 4 ; (* rest1=nil → safety *)
                          tLam Examples.nat_ty ( (* b *)
                            tLam list_ty (       (* rest2 *)
                              (* exec code_tail (cons (plus a b) rest2) *)
                              tApp (tApp (tVar 8) (tVar 4))
                                   (cons (tApp (tApp Examples.plus (tVar 3)) (tVar 1))
                                         (tVar 0))
                            ))
                        ])
                    ]) ;
                  (* head ≠ 0 → PUSH: exec code_tail (cons head stack) *)
                  tLam Examples.nat_ty ( (* tVar 0 = n, head=succ n *)
                    tApp (tApp (tVar 5) (tVar 1))
                         (cons (tVar 2) (tVar 3))
                  )
                ]))
            ]]))).

  (** Convenience: list notation in the object language. *)
  Fixpoint list_lit (xs : list tm) : tm :=
    match xs with
    | [] => nil
    | x :: xs => cons x (list_lit xs)
    end.

End ListNat.
