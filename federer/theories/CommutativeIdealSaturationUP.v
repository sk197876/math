(** Federer (1969), 3.4.8(10), p. 331:
    multiplication by a power of the
    original delta sends an ideal member
    into the equation ideal. Specify this
    auxiliary saturation by exact membership
    before any construction or ideal theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_commutative_ideal_saturation]: the
    original assertion that delta to some
    finite power times sigma belongs to
    the equation ideal F, 3.4.8(10),
    p. 331. Exponent zero is allowed
    in this auxiliary predicate; ideal absorption
    supplies a positive exponent when needed. *)
Definition is_commutative_ideal_saturation (A:comNzRingType) (I:set A) (delta:A) (S:set A):Prop:=
  forall x:A,S x <->exists u:nat,I (delta^+u*x).
