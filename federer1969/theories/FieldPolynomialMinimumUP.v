(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the original minimal polynomial
    is monic and generates the evaluation kernel.
    These independent laws precede its existence.
    Source: Bourbaki, Algebra II (1990), Chapter V,
    section 3, no. 1, Theorem 1(a), p. V.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialMonicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_minimal_field_polynomial]: the monic
    kernel generator in Bourbaki (1990), Chapter V,
    section 3, no. 1, Theorem 1(a), p. V.16;
    supporting 3.4.8(8), pp. 329–330. No
    prime or separability conclusion is included. *)
Record is_minimal_field_polynomial (K:fieldType) (B:comNzRingType) (L:fieldType)
  (coefficient:B->nat->K) (E:{rmorphism B->L}) (H:B) n:Prop:={
  (** Source for [minimal_field_polynomial_positive]: the
      original algebraic degree is positive in
      the cited definition preceding Theorem 1. *)
  minimal_field_polynomial_positive:(0<n)%N;
  (** Source for [minimal_field_polynomial_monic]: the
      original polynomial is monic of degree n
      in the cited definition. *)
  minimal_field_polynomial_monic:is_monic_polynomial coefficient H n;
  (** Source for [minimal_field_polynomial_vanishes]: the
      original evaluation is zero in the cited theorem. *)
  minimal_field_polynomial_vanishes:E H = 0;
  (** Source for [minimal_field_polynomial_kernel]: exact
      generation of the evaluation kernel in
      the cited Theorem 1(a). *)
  minimal_field_polynomial_kernel:forall P:B,E P = 0 <->commutative_divides H P
}.
