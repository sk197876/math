(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    original prepared polynomial is a finite product of
    actual analytic primes. Gauss factorization, specialization
    at the origin, and original division prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormDifferentialUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermValueSealed ComplexWeierstrassTransverseUP
  ComplexWeierstrassTransversePullback CommutativeDomainUP CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  PolynomialCoefficientMapSealed GaussPolynomialFactorization DistinguishedPolynomialUP
  DistinguishedPolynomialFactorization HolomorphicDistinguishedPolynomialPrime.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ActualFactorization.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Hypothesis hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi).
Hypothesis hXiValues:forall x,holomorphic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation E:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).
Local Notation value:=(@HolomorphicGermValue.map R K NK (complex_norm_real hNK) (projection 0)).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.


(** Source for [holomorphic_distinguished_polynomial_factorization]: the
    original distinguished polynomial factors into genuine
    analytic primes, expanding the induction of 3.4.7,
    p. 325. Coefficient unique factorization is the induction
    premise on the actual lower-dimensional transverse space. *)
Theorem holomorphic_distinguished_polynomial_factorization
    (hUFD:is_unique_factorization_commutative_domain A) (P:B) k:
  is_distinguished_polynomial coefficient value P k ->
  exists F:seq G,(forall p,p\in F ->is_commutative_prime_element p) /\
    J P = \prod_(p<-F) p.
Proof.
move=>hDistinguished.
pose D:comNzRingType:=@CommutativePolynomial.space (ComplexScalars.C R).
pose embedR:{rmorphism (ComplexScalars.C R)->D}:=@CommutativePolynomial.embed (ComplexScalars.C R).
pose variableR:D:=@CommutativePolynomial.variable (ComplexScalars.C R).
pose target:=@CommutativePolynomial.coefficient (ComplexScalars.C R).
have hTarget:=@CommutativePolynomial.laws (ComplexScalars.C R).
pose M:{rmorphism B->D}:=@PolynomialCoefficientMap.map A B (ComplexScalars.C R) D embed variable coefficient
  embedR variableR target hP hTarget value.
have hMap:=@PolynomialCoefficientMap.laws A B (ComplexScalars.C R) D embed variable coefficient
  embedR variableR target hP hTarget value.
have hDomainR:is_commutative_integral_domain (ComplexScalars.C R).
  move=>x y /eqP;rewrite mulf_eq0=>/orP[/eqP h|/eqP h];[by left|by right].
have hPolynomialUFD:=@gauss_polynomial_prime_factorization A B embed variable coefficient hP hUFD.
apply:(@distinguished_polynomial_prime_factorization A B (ComplexScalars.C R) D G embed variable coefficient hP
  embedR variableR target hTarget value M hMap hUFD.1 hDomainR hPolynomialUFD J _ k P hDistinguished).
move=>H n hH hPrimeH.
exact:(@holomorphic_distinguished_polynomial_prime R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ
  hUFD.1 H n hH hPrimeH).
Qed.
End ActualFactorization.
