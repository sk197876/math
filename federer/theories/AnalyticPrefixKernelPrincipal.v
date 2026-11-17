(** Federer (1969), 3.4.8(10), p. 331:
    the first prefix step reduces an
    original ideal member to a bounded
    polynomial remainder. The original polynomial
    kernel and degree bound force that
    remainder to be zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct EuclideanScalarCoordinateMaps
  EuclideanStiefelInnerSplitting OrthonormalFamilies OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives AnalyticGermValueSealed AnalyticCoordinateGermsSealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixGermInjective
  AnalyticPrefixNestedComposition AnalyticPrefixCoordinateGerm AnalyticPrefixWeierstrassSplit
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionCoordinateRegularWitness
  AnalyticOriginalPreparedPolynomial WeierstrassRegularUP WeierstrassFunctionalPower
  CommutativeIdealUP NoetherianRingSurjection CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed CommutativePolynomialEvaluationLaws PolynomialScalarComposition
  DistinguishedPolynomialUP AnalyticPrefixGermSubring AnalyticOriginalPolynomialDivision AnalyticPrefixPolynomialDivision
  AnalyticGermDomain CommutativeFactorizationUP PolynomialMonicPrimeBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixKernel.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable m:'I_n.
Local Notation Y:=(R_n R (m:nat).+1).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (m:nat).+1)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (m:nat).+1)).
Local Notation Z:=(R_n R (m:nat)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (m:nat))).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (m:nat))).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R Z NZ hNZ 0)].
Local Notation A1:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation hMN:=(leq_trans (leqnSn (m:nat)) (ltn_ord m)).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation E1:=(@analytic_prefix_germ_map R X NX hNX n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation Gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega m).
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.



(** Source for [analytic_prefix_polynomial_kernel_principal]:
    supporting first step of the original
    coordinate induction in 3.4.8(10), p. 331.
    Original analytic division and the proved
    polynomial kernel show that every original
    prefix ideal member is an actual
    analytic multiple of W_(m+1). The
    quotient remains in the same prefix. *)
Theorem analytic_prefix_polynomial_kernel_principal (I:set G) (H:P) k:
  is_commutative_ideal I ->
  is_distinguished_polynomial coefficient (@AnalyticGermValue.map R Z NZ hNZ 0) H k ->
  (0<k)%N ->(forall W:P,I (J W) <->commutative_divides H W) ->
  forall alpha:G,I alpha ->
    @analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) alpha ->
  exists a:G,
    @analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) a /\alpha = a*J H.
Proof.
move=>hI hDistinguished hK hKernel alpha hAlpha hPrefix.
have [a [r [hSupport [hDivision hQuotient]]]]:=@analytic_prefix_distinguished_division
  R X B hB n e he omega m P embed variable coefficient hP J hJ H k hDistinguished hK alpha hPrefix.
have hInH:I (J H).
  apply:(hKernel H).2;exists 1;by rewrite mul1r.
have hProduct:I (a*J H):=@commutative_ideal_mul G I hI a (J H) hInH.
have hRemainder:I (J r).
  have hDifference:=@commutative_ideal_add G I hI alpha (-(a*J H)) hAlpha
    (@commutative_ideal_opp G I hI _ hProduct).
  by rewrite hDivision addrAC subrr add0r in hDifference.
have hDivides:commutative_divides H r:=(hKernel r).1 hRemainder.
have hDomain:=@analytic_germ_no_zero_divisors R Z NZ hNZ 0.
have hZero:=@polynomial_bounded_divisible_zero A P embed variable coefficient hP hDomain H r k
  hDistinguished.1.1 hSupport hDivides.
exists a;split;first exact:hQuotient.
by rewrite hDivision hZero rmorph0 addr0.
Qed.
End PrefixKernel.
