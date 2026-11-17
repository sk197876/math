(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: a common divisor specified by
    its two divisibility laws and a Bezout identity.
    The laws precede existence and select no
    principal generator. Source: Bourbaki, Algebra II
    (1990), Chapter IV, section 1, no. 4,
    pp. IV.11–12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_commutative_bezout_gcd]: the common
    divisor and linear-combination characterisation in
    Bourbaki (1990), Chapter IV, section 1,
    no. 4, pp. IV.11–12, supporting the
    simplicity argument of 3.4.8(8), pp. 329–330. *)
Record is_commutative_bezout_gcd (A:comNzRingType) (P Q G:A):Prop:={
  (** Source for [bezout_gcd_divides_left]: the
      common divisor divides the first original element. *)
  bezout_gcd_divides_left:commutative_divides G P;
  (** Source for [bezout_gcd_divides_right]: the
      common divisor divides the second original element. *)
  bezout_gcd_divides_right:commutative_divides G Q;
  (** Source for [bezout_gcd_combination]: the
      common divisor is an original two-generator
      combination in the cited characterisation. *)
  bezout_gcd_combination:exists U V:A,G = U*P+V*Q
}.
