(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: a bounded coefficient witness can be
    shifted to any larger degree, with its leading
    coefficient unchanged. This is the degree-reduction step
    in Hilbert's theorem; Bourbaki, Commutative Algebra (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP
  PolynomialPowerShift PolynomialTruncatedLeadingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [truncated_polynomial_leading_lift]: the
    actual variable-power multiple supplies a polynomial of
    the required higher degree bound with the same
    specified coefficient; Hilbert's theorem, Bourbaki (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184,
    supporting the expanded algebra for 3.4.8(5), p. 328. *)
Lemma truncated_polynomial_leading_lift (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (P:B) N d:
  (N<=d)%N ->(forall i,(N<i)%N ->coefficient P i = 0) ->
  (forall i,(d<i)%N ->coefficient (variable^+(d-N)%N*P) i = 0) /\
    coefficient (variable^+(d-N)%N*P) d = coefficient P N.
Proof.
move=>hND hHigh;split.
- move=>i hi;rewrite (@polynomial_variable_power_multiply_coefficient A B embed variable coefficient hP).
  have hSmall:(d-N<=i)%N:=leq_trans (leq_subr N d) (ltnW hi).
  rewrite hSmall;apply:hHigh.
  by rewrite ltn_subRL (subnK hND).
- rewrite (@polynomial_variable_power_multiply_coefficient A B embed variable coefficient hP)
    (leq_subr N d).
  congr (coefficient P _).
  by rewrite (subKn hND).
Qed.
