(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the existing finite polynomial
    interpolation theorem supplies the formal derivative.
    Source: Bourbaki, Algebra II (1990), Chapter IV,
    section 2, no. 2, pp. IV.17–18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialFiniteSums FormalPolynomialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [formal_polynomial_derivative_exists]: the
    formal derivative in Bourbaki (1990), Chapter IV,
    section 2, no. 2, pp. IV.17–18.
    Apply existing finite interpolation to its
    independently prescribed coefficients. *)
Theorem formal_polynomial_derivative_exists (A B:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B):
  exists D:B,is_formal_polynomial_derivative coefficient P D.
Proof.
have [N hN]:=@polynomial_coefficients_finite A B embed variable coefficient hP P.
apply:(@polynomial_interpolation_exists A B embed variable coefficient hP
  (fun i=>i.+1%:R*coefficient P i.+1)).
exists N=>i hi;rewrite hN ?mulr0 //.
exact:leq_trans hi (leqnSn i).
Qed.

(** Source for [formal_polynomial_derivative_unique]: the
    derivative coefficient equation determines the
    polynomial uniquely, supporting the cited formal
    differentiation used in 3.4.8(8), pp. 329–330. *)
Lemma formal_polynomial_derivative_unique (A B:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (P D E:B):
  is_formal_polynomial_derivative coefficient P D ->
  is_formal_polynomial_derivative coefficient P E ->D = E.
Proof.
move=>hD hE;apply:(@polynomial_coefficients_unique A B embed variable coefficient hP)=>i.
by rewrite hD hE.
Qed.
