(** Federer (1969), 3.4.7, p. 325: uniqueness of
    prime factorization is up to multiplication by units
    and permutation. The association relation is specified
    independently of a factorization construction. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_commutative_associate]: original factors
    are associated when one is a unit multiple
    of the other, supporting the uniqueness assertion
    in 3.4.7, p. 325. *)
Definition is_commutative_associate (A:comNzRingType) (x y:A):Prop:=
  exists u:A,is_commutative_unit u /\x = u*y.
