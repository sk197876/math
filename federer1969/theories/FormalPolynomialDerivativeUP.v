(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: formal differentiation over the
    coefficient field used for separability. State its
    coefficient equation before existence or selection.
    Source: Bourbaki, Algebra II (1990), Chapter IV,
    section 2, no. 2, pp. IV.17–18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_formal_polynomial_derivative]: the
    original coefficient differentiation law in Bourbaki
    (1990), Chapter IV, section 2, no. 2,
    pp. IV.17–18; supporting separability in
    3.4.8(8), pp. 329–330. This is algebraic
    differentiation over any commutative coefficient ring. *)
Definition is_formal_polynomial_derivative (A:comNzRingType) (B:Type)
  (coefficient:B->nat->A) (P D:B):Prop:=
  forall i,coefficient D i = i.+1%:R*coefficient P i.+1.
