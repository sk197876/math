(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: multiplying a polynomial by a variable
    power shifts its coefficients without changing them.
    This supports the degree reduction in Hilbert's theorem;
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 2, no. 10, Corollary 1, p. 184. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_variable_power_multiply_coefficient]:
    the exact power-shift coefficient equation in the
    elementary coefficient proof of Hilbert's theorem;
    Bourbaki (1972), Chapter III, section 2, no. 10,
    Corollary 1, p. 184, supporting 3.4.8(5), p. 328. *)
Lemma polynomial_variable_power_multiply_coefficient (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient) s (P:B) i:
  coefficient (variable^+s*P) i =
    if (s<=i)%N then coefficient P (i-s)%N else 0.
Proof.
elim:s i=>[i|s ih [|i]].
- by rewrite expr0 mul1r subn0.
- by rewrite exprS -mulrA
    (@polynomial_variable_multiply_coefficient A B embed variable coefficient hP).
- rewrite exprS -mulrA
    (@polynomial_variable_multiply_coefficient A B embed variable coefficient hP) /= subSS subn0 ih.
  by [].
Qed.
