(** Federer (1969), 3.4.7, p. 325: the
    original prepared polynomial is a finite product of
    actual analytic primes. Gauss factorization, specialization
    at the origin, and original division prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueSealed WeierstrassTransverseUP
  WeierstrassTransversePullback CommutativeDomainUP CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  PolynomialCoefficientMapSealed GaussPolynomialFactorization DistinguishedPolynomialUP
  DistinguishedPolynomialFactorization AnalyticDistinguishedPolynomialPrime.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ActualFactorization.
Variable R:realType.
Variables X K:lmodType R.
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Variable v:X.
Variable xi:Hom X R^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Hypothesis hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Hypothesis hXiValues:forall x,analytic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).
Local Notation value:=(@AnalyticGermValue.map R K NK hNK (projection 0)).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.


(** Source for [analytic_distinguished_polynomial_factorization]: the
    original distinguished polynomial factors into genuine
    analytic primes, expanding the induction of 3.4.7,
    p. 325. Coefficient unique factorization is the induction
    premise on the actual lower-dimensional transverse space. *)
Theorem analytic_distinguished_polynomial_factorization
    (hUFD:is_unique_factorization_commutative_domain A) (P:B) k:
  is_distinguished_polynomial coefficient value P k ->
  exists F:seq G,(forall p,p\in F ->is_commutative_prime_element p) /\
    J P = \prod_(p<-F) p.
Proof.
move=>hDistinguished.
pose D:comNzRingType:=@CommutativePolynomial.space R.
pose embedR:{rmorphism R->D}:=@CommutativePolynomial.embed R.
pose variableR:D:=@CommutativePolynomial.variable R.
pose target:=@CommutativePolynomial.coefficient R.
have hTarget:=@CommutativePolynomial.laws R.
pose M:{rmorphism B->D}:=@PolynomialCoefficientMap.map A B R D embed variable coefficient
  embedR variableR target hP hTarget value.
have hMap:=@PolynomialCoefficientMap.laws A B R D embed variable coefficient
  embedR variableR target hP hTarget value.
have hDomainR:is_commutative_integral_domain R.
  move=>x y /eqP;rewrite mulf_eq0=>/orP[/eqP h|/eqP h];[by left|by right].
have hPolynomialUFD:=@gauss_polynomial_prime_factorization A B embed variable coefficient hP hUFD.
apply:(@distinguished_polynomial_prime_factorization A B R D G embed variable coefficient hP
  embedR variableR target hTarget value M hMap hUFD.1 hDomainR hPolynomialUFD J _ k P hDistinguished).
move=>H n hH hPrimeH.
exact:(@analytic_distinguished_polynomial_prime R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ
  hUFD.1 H n hH hPrimeH).
Qed.
End ActualFactorization.
