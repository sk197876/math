(** Federer (1969), 3.4.7, p. 325: extract a
    monic prime from the original prepared polynomial.
    The remaining distinguished factor has smaller degree.
    Both factors retain the original transverse specialization. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP
  CommutativePrimeLaws CommutativePrimeTransport CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialProductDegree CommutativePolynomialMonicUP
  PolynomialMonicPrimeBounds PolynomialMonicFactorNormalization
  PolynomialCoefficientMapUP DistinguishedPolynomialUP DistinguishedPolynomialSpecialization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distinguished_polynomial_prime_step]: the
    original Gauss factorization gives a prime factor
    and a smaller-degree distinguished quotient, expanding
    the unique-factorization proof in 3.4.7, p. 325.
    The value homomorphism need not be injective. *)
Theorem distinguished_polynomial_prime_step (A B C D:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
    (hTarget:is_commutative_polynomial_ring embedC variableC target)
    (value:{rmorphism A->C}) (M:{rmorphism B->D})
    (hMap:is_polynomial_coefficient_map coefficient target value M)
    (hDomain:is_commutative_integral_domain A)
    (hDomainC:is_commutative_integral_domain C)
    (hUFD:is_unique_factorization_commutative_domain B) (P:B) k:
  is_distinguished_polynomial coefficient value P k ->(0<k)%N ->
  exists H Q:B,exists m n:nat,
    is_distinguished_polynomial coefficient value H m /\
    is_commutative_prime_element H /\
    is_distinguished_polynomial coefficient value Q n /\
    (n<k)%N /\P = H*Q.
Proof.
move=>hDistinguished hPositive.
have hNonzero:P<>0.
  move=>hZero;have hLeading:=hDistinguished.1.1.1.
  apply:hLeading;rewrite hZero.
  exact:(@polynomial_coefficient_zero A B embed variable coefficient hP k).
have hNonunit:=@polynomial_positive_degree_not_unit A B embed variable coefficient
  hP hDomain P k hDistinguished.1.1 hPositive.
have [H [hPrime [Q hProduct]]]:=@commutative_nonunit_prime_divisor B hUFD P hNonzero hNonunit.
have hHNonzero:H<>0:=hPrime.1.
have hQNonzero:Q<>0 by move=>hZero;apply:hNonzero;by rewrite hProduct hZero mul0r.
have [m hDegreeH]:=@polynomial_degree_exists A B embed variable coefficient hP H hHNonzero.
have [n hDegreeQ]:=@polynomial_degree_exists A B embed variable coefficient hP Q hQNonzero.
have hRestore:P = H*Q by rewrite hProduct mulrC.
have [H' [Q' [u [w [hMonicH [hMonicQ [hProduct' [hU [hW [hH' hQ']]]]]]]]]]:=
  @polynomial_monic_factor_normalization A B embed variable coefficient hP hDomain
    P H Q k m n hDistinguished.1 hDegreeH hDegreeQ hRestore.
have hPrime':is_commutative_prime_element H'.
  exact:(commutative_prime_associate_transport hPrime (commutative_ring_map_unit embed hU) hH').
have hPositiveM:=@polynomial_monic_prime_positive_degree A B embed variable coefficient
  hP H' m hMonicH hPrime'.
have hDegreeProduct:=@polynomial_product_degree A B embed variable coefficient hP hDomain
  H' Q' m n hMonicH.1 hMonicQ.1.
rewrite hProduct' in hDegreeProduct.
have hDegreeSum:=@polynomial_degree_unique A B coefficient P (m+n)%N k
  hDegreeProduct hDistinguished.1.1.
have hSmaller:(n<k)%N.
  rewrite -hDegreeSum -[n]add0n ltn_add2r;exact:hPositiveM.
have [hDistinguishedH hDistinguishedQ]:=
  @distinguished_polynomial_monic_factors A B C D coefficient embedC variableC target
    hTarget value M hMap hDomainC P H' Q' k m n hDistinguished hMonicH hMonicQ (esym hProduct').
exists H',Q',m,n;split;first exact:hDistinguishedH.
split;first exact:hPrime'.
split;first exact:hDistinguishedQ.
split;[exact:hSmaller|exact:esym hProduct'].
Qed.
