(** Federer (1969), 3.4.8(8), p. 329:
    an original element is integral over the
    coefficient ring when a monic finite relation
    holds. This definition selects no polynomial or
    generator family and assumes no extension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_integral_ring_element]: integral
    dependence used in 3.4.8(8), p. 329,
    expressed by a monic relation with original
    scalar coefficients. Moving its lower terms to
    the other side changes only their signs.
    Compare Bourbaki, Commutative Algebra (1972),
    Chapter V, section 1, no. 1, p. 303. *)
Definition is_integral_ring_element (A C:comNzRingType)
  (phi:{rmorphism A->C}) (x:C):Prop:=
  exists k (c:nat->A),(0<k)%N /\x^+k = \sum_(i<k) phi (c i)*x^+(i:nat).
