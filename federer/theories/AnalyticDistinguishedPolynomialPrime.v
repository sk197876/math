(** Federer (1969), 3.4.7, p. 325: a prime
    distinguished factor in the original transverse polynomial
    subring is prime in the actual analytic germ ring.
    The original division theorem, actual finite remainders,
    coefficient independence, and uniqueness prove the lift. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueSealed WeierstrassTransverseUP
  WeierstrassTransversePullback AnalyticTransversePolynomialInjection
  AnalyticDistinguishedPolynomialLine AnalyticPolynomialDivisionModel
  CommutativeDomainUP CommutativeFactorizationUP CommutativePolynomialUP
  CommutativePolynomialEvaluationUP DistinguishedPolynomialUP PolynomialMonicPrimeBounds
  PolynomialPrimeDivisionLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ActualPrime.
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

(** Source for [analytic_distinguished_polynomial_prime]: an
    original distinguished polynomial prime remains prime
    among all analytic germs, expanding the final factor
    comparison in 3.4.7, p. 325. Analytic
    primality, finite remainder membership, and a unique
    remainder comparison are all conclusions of earlier proofs,
    rather than new analytic hypotheses. *)
Theorem analytic_distinguished_polynomial_prime
    (hDomain:is_commutative_integral_domain A) (H:B) n:
  is_distinguished_polynomial coefficient value H n ->
  is_commutative_prime_element H ->is_commutative_prime_element (J H).
Proof.
move=>hDistinguished hPrime.
have hPositive:=@polynomial_monic_prime_positive_degree A B embed variable coefficient
  hP H n hDistinguished.1 hPrime.
have hRegular:=@analytic_distinguished_polynomial_regular R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXiValues B embed variable coefficient hP J hJ
  H n hDistinguished hPositive.
have hInjective:=@analytic_transverse_polynomial_evaluation_injective R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi B embed variable coefficient hP J hJ hXiValues.
apply:(@polynomial_prime_unique_division_lift A B G embed variable coefficient
  hP hDomain H n J hInjective hDistinguished.1 hPrime).
- exact:(@analytic_polynomial_division_exists R X K NX NK hNX hNK v xi inclusion projection
    hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ H n hRegular).
- exact:(@analytic_polynomial_zero_remainder_unique R X K NX NK hNX hNK v xi inclusion projection
    hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ H n hRegular).
Qed.
End ActualPrime.
