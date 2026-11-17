(** Federer (1969), 3.4.7, p. 325: polynomial
    products have the sum of the actual factor
    degrees over a domain. This supports the Gauss argument. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP
  CommutativePolynomialDegree NaturalConvolution NaturalConvolutionDegree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Products.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Hypothesis hDomain:is_commutative_integral_domain A.

(** Source for [polynomial_product_degree]: original nonzero
    leading coefficients multiply, and degrees add,
    supporting 3.4.7, p. 325. *)
Theorem polynomial_product_degree (P Q:B) m n:
  is_polynomial_degree coefficient P m ->is_polynomial_degree coefficient Q n ->
  is_polynomial_degree coefficient (P*Q) (m+n)%N.
Proof.
move=>[hPm hPHigh] [hQn hQHigh].
have hConvolution k:coefficient (P*Q) k =
    natural_coefficient_convolution (coefficient P) (coefficient Q) k.
  rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
  by rewrite /natural_coefficient_convolution big_mkord.
split.
- rewrite hConvolution (natural_convolution_leading_coefficient hPHigh hQHigh).
  exact:(@commutative_domain_product_nonzero A hDomain (coefficient P m) (coefficient Q n) hPm hQn).
- move=>i hi;rewrite hConvolution.
  exact:natural_convolution_above_degree hPHigh hQHigh hi.
Qed.

(** Source for [polynomial_ring_domain]: the polynomial
    extension of an original domain has no zero
    divisors, supporting 3.4.7, p. 325. *)
Theorem polynomial_ring_domain:is_commutative_integral_domain B.
Proof.
move=>P Q hProduct;case:(eqVneq P 0)=>[h|hP0];first by left.
case:(eqVneq Q 0)=>[h|hQ0];first by right.
have hPNonzero:P<>0 by apply/eqP;exact:hP0.
have hQNonzero:Q<>0 by apply/eqP;exact:hQ0.
have [m hM]:=@polynomial_degree_exists A B embed variable coefficient hP P hPNonzero.
have [n hN]:=@polynomial_degree_exists A B embed variable coefficient hP Q hQNonzero.
have [hLeading _]:=polynomial_product_degree hM hN.
exfalso;apply:hLeading;rewrite hProduct.
exact:(@polynomial_coefficient_zero A B embed variable coefficient hP (m+n)%N).
Qed.
End Products.
