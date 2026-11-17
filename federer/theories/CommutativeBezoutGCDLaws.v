(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the Bezout identity proves the
    greatest-divisor law and survives coefficient extension.
    Reuse the existing divisibility arithmetic. Source:
    Bourbaki, Algebra II (1990), Chapter IV,
    section 1, no. 4, pp. IV.11–12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativeDivisibility CommutativeBezoutGCDUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_bezout_gcd_greatest]: each
    original common divisor divides the Bezout
    combination, the greatest-divisor assertion in
    the cited characterisation. *)
Theorem commutative_bezout_gcd_greatest (A:comNzRingType) (P Q G:A):
  is_commutative_bezout_gcd P Q G ->forall d:A,
  commutative_divides d P ->commutative_divides d Q ->commutative_divides d G.
Proof.
move=>hG d hP hQ;have [U [V ->]]:=bezout_gcd_combination hG.
apply:commutative_divides_add.
- exact:commutative_divides_multiply hP.
- exact:commutative_divides_multiply hQ.
Qed.

(** Source for [commutative_bezout_gcd_ring_map]: the
    original divisor and Bezout equations are
    preserved under a ring homomorphism, supporting
    coefficient descent in 3.4.8(8), pp. 329–330. *)
Theorem commutative_bezout_gcd_ring_map (A B:comNzRingType) (f:{rmorphism A->B}) (P Q G:A):
  is_commutative_bezout_gcd P Q G ->is_commutative_bezout_gcd (f P) (f Q) (f G).
Proof.
move=>hG;constructor.
- have [U hP]:=bezout_gcd_divides_left hG;exists (f U);by rewrite -rmorphM -hP.
- have [V hQ]:=bezout_gcd_divides_right hG;exists (f V);by rewrite -rmorphM -hQ.
- have [U [V hCombination]]:=bezout_gcd_combination hG.
  exists (f U),(f V);by rewrite -!rmorphM -rmorphD -hCombination.
Qed.

(** Source for [commutative_bezout_gcd_kernel]: an
    original evaluation annihilates the Bezout gcd
    exactly when it annihilates both original
    polynomials, supporting common-root comparison
    in 3.4.8(8), pp. 329–330. *)
Theorem commutative_bezout_gcd_kernel (A C:comNzRingType)
  (E:{rmorphism A->C}) (P Q G:A):
  is_commutative_bezout_gcd P Q G ->(E G = 0 <->E P = 0 /\E Q = 0).
Proof.
move=>hG;split.
- move=>hZero;have [U hP]:=bezout_gcd_divides_left hG.
  have [V hQ]:=bezout_gcd_divides_right hG;split.
  + by rewrite hP rmorphM hZero mulr0.
  + by rewrite hQ rmorphM hZero mulr0.
- move=>[hP hQ];have [U [V hCombination]]:=bezout_gcd_combination hG.
  by rewrite hCombination rmorphD !rmorphM hP hQ !mulr0 add0r.
Qed.
