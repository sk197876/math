(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: products of ideals are specified as the
    least ideals containing all original products. These
    laws support the Rees ring and Artin–Rees argument;
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_commutative_ideal_product]: the least-ideal
    definition of an ideal product used in the Rees
    ring and Artin–Rees argument, Bourbaki (1972),
    Chapter III, section 3, no. 1, pp. 195–197,
    supporting the expanded algebra for 3.4.8(5), p. 328. *)
Definition is_commutative_ideal_product (A:comNzRingType) (I J K:set A):Prop:=
  is_generated_commutative_ideal
    [set x:A|exists a b,I a /\J b /\x=a*b] K.
