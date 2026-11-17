(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: powers of an ideal are specified by
    their zero and successor laws. The laws precede
    existence and sealing. Source: Bourbaki, Commutative
    Algebra (1972), Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_commutative_ideal_power_family]: the
    original ideal-power laws used in the cited Rees
    and Artin–Rees arguments, supporting 3.4.8(5), p. 328. *)
Record is_commutative_ideal_power_family (A:comNzRingType) (I:set A)
    (P:nat->set A):Prop:={
  (** Source for [commutative_ideal_power_zero]: power zero
      is the whole ring, supporting the cited arguments. *)
  commutative_ideal_power_zero:P 0%N=setT;
  (** Source for [commutative_ideal_power_successor]: each
      successor power is the specified ideal product,
      supporting the cited arguments. *)
  commutative_ideal_power_successor:forall n,
    is_commutative_ideal_product I (P n) (P n.+1)
}.
