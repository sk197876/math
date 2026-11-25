(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: prime polynomial factors give prime
    principal ideals in the root extensions used by
    the finite-separable argument. Reuse the existing
    divisibility laws from 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeFactorizationUP CommutativeDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [commutative_principal_prime_ideal]: a
    prime element generates a proper prime ideal,
    supporting the classical finite-separable argument
    in 3.4.8(8), pp. 329–330. Both primeness
    specifications were already defined in 3.4.5–7. *)
Theorem commutative_principal_prime_ideal (A:comNzRingType) (p:A):
  is_commutative_prime_element p ->is_prime_commutative_ideal (commutative_divides p).
Proof.
move=>hPrime;split.
- constructor.
  + exact:commutative_divides_zero.
  + move=>x y;exact:commutative_divides_add.
  + move=>x;exact:commutative_divides_negate.
  + move=>x y;exact:commutative_divides_multiply.
split.
- move=>hOne;exact:hPrime.2.1 ((@commutative_divides_one_unit A p).1 hOne).
- exact:hPrime.2.2.
Qed.
