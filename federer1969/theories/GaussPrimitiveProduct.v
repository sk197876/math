(** Federer (1969), 3.4.7, p. 325: the primitive
    product step of the invoked Gauss lemma, proved
    from actual finite coefficients and prime divisibility. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialUP
  CommutativePolynomialDegreeUP FirstNondivisibleCoefficient
  NaturalConvolution PrimeConvolutionCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [gauss_primitive_product]: a product of
    primitive polynomials is primitive, supporting the Gauss
    lemma invoked in 3.4.7, p. 325. The
    proof uses the first coefficient not divisible by
    each original prime; it assumes no polynomial UFD theorem. *)
Theorem gauss_primitive_product (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient) (P Q:B):
  is_primitive_polynomial coefficient (@is_commutative_prime_element A) (@commutative_divides A) P ->
  is_primitive_polynomial coefficient (@is_commutative_prime_element A) (@commutative_divides A) Q ->
  is_primitive_polynomial coefficient (@is_commutative_prime_element A) (@commutative_divides A) (P*Q).
Proof.
move=>hPPrimitive hQPrimitive p hPrime.
have [i [hI hLowerP]]:=first_nondivisible_coefficient (hPPrimitive p hPrime).
have [j [hJ hLowerQ]]:=first_nondivisible_coefficient (hQPrimitive p hPrime).
exists (i+j)%N.
have hCoefficient:coefficient (P*Q) (i+j)%N =
    natural_coefficient_convolution (coefficient P) (coefficient Q) (i+j)%N.
  rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
  by rewrite /natural_coefficient_convolution big_mkord.
rewrite hCoefficient.
exact:(@prime_convolution_first_coefficient A p (coefficient P) (coefficient Q)
  i j hPrime hI hJ hLowerP hLowerQ).
Qed.
