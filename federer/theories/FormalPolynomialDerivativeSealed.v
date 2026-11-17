(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the proved formal derivative
    behind its opaque coefficient specification.
    Source: Bourbaki, Algebra II (1990), Chapter IV,
    section 2, no. 2, pp. IV.17–18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP FormalPolynomialDerivativeUP FormalPolynomialDerivativeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FormalPolynomialDerivativeSignature.
(** Source for [value]: the formal derivative in
    the cited differentiation criterion, supporting
    3.4.8(8), pp. 329–330. *)
Parameter value:forall (A B:comNzRingType) (embed:{rmorphism A->B}) (variable:B)
  (coefficient:B->nat->A),is_commutative_polynomial_ring embed variable coefficient ->B->B.
(** Source for [laws]: the independent original
    derivative coefficient equation in the cited source. *)
Parameter laws:forall (A B:comNzRingType) (embed:{rmorphism A->B}) (variable:B)
  (coefficient:B->nat->A) (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B),
  is_formal_polynomial_derivative coefficient P (@value A B embed variable coefficient hP P).
End FormalPolynomialDerivativeSignature.
Module FormalPolynomialDerivative:FormalPolynomialDerivativeSignature.
(** Source for [value]: hidden choice from proved
    finite interpolation, supporting the cited formal derivative. *)
Definition value (A B:comNzRingType) (embed:{rmorphism A->B}) (variable:B)
  (coefficient:B->nat->A) (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B):B:=
  projT1 (cid (@formal_polynomial_derivative_exists A B embed variable coefficient hP P)).
(** Source for [laws]: the selected derivative
    satisfies its independent coefficient equation. *)
Lemma laws (A B:comNzRingType) (embed:{rmorphism A->B}) (variable:B)
  (coefficient:B->nat->A) (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B):
  is_formal_polynomial_derivative coefficient P (@value A B embed variable coefficient hP P).
Proof. exact:(projT2 (cid (@formal_polynomial_derivative_exists A B embed variable coefficient hP P))). Qed.
End FormalPolynomialDerivative.
