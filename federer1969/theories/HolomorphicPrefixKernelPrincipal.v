(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    the first prefix step reduces an
    original ideal member to a bounded
    polynomial remainder. The original polynomial
    kernel and degree bound force that
    remainder to be zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct EuclideanScalarCoordinateMaps
  EuclideanStiefelInnerSplitting OrthonormalFamilies OrthogonalGroupTopology HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives HolomorphicGermValueSealed HolomorphicCoordinateGermsSealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicPrefixGermInjective
  HolomorphicPrefixNestedComposition HolomorphicPrefixCoordinateGerm HolomorphicCoordinatePrefixSplit
  HolomorphicRotatedGermIdeal HolomorphicReductionActual HolomorphicPrefixRegularWitness
  HolomorphicOriginalPreparedPolynomial ComplexWeierstrassRegularUP ComplexWeierstrassFunctionalPower
  CommutativeIdealUP NoetherianRingSurjection CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed CommutativePolynomialEvaluationLaws PolynomialScalarComposition
  DistinguishedPolynomialUP HolomorphicPrefixGermSubring HolomorphicOriginalPolynomialDivision HolomorphicPrefixPolynomialDivision
  HolomorphicGermDomain CommutativeFactorizationUP PolynomialMonicPrimeBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixKernel.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Variable m:'I_n.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) (m:nat).+1).
Local Notation NY:=(@holomorphic_coordinate_norm R (m:nat).+1).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (m:nat).+1)).
Local Notation Z:=(coordinate_space (ComplexScalars.C R) (m:nat)).
Local Notation NZ:=(@holomorphic_coordinate_norm R (m:nat)).
Local Notation hNZ:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (m:nat))).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R Z NZ hNZ 0)].
Local Notation A1:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation hMN:=(leq_trans (leqnSn (m:nat)) (ltn_ord m)).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Local Notation E1:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation Gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega m).
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.



(** Source for [holomorphic_prefix_polynomial_kernel_principal]:
    supporting first step of the original
    coordinate induction in 3.4.8(10), p. 331.
    Original holomorphic division and the proved
    polynomial kernel show that every original
    prefix ideal member is an actual
    holomorphic multiple of W_(m+1). The
    quotient remains in the same prefix. *)
Theorem holomorphic_prefix_polynomial_kernel_principal (I:set G) (H:P) k:
  is_commutative_ideal I ->
  is_distinguished_polynomial coefficient (@HolomorphicGermValue.map R Z NZ hNZ 0) H k ->
  (0<k)%N ->(forall W:P,I (J W) <->commutative_divides H W) ->
  forall alpha:G,I alpha ->
    @holomorphic_prefix_germ_subring R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m) alpha ->
  exists a:G,
    @holomorphic_prefix_germ_subring R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m) a /\alpha = a*J H.
Proof.
move=>hI hDistinguished hK hKernel alpha hAlpha hPrefix.
have [a [r [hSupport [hDivision hQuotient]]]]:=@holomorphic_prefix_distinguished_division
  R X Herm hHerm n e he omega m P embed variable coefficient hP J hJ H k hDistinguished hK alpha hPrefix.
have hInH:I (J H).
  apply:(hKernel H).2;exists 1;by rewrite mul1r.
have hProduct:I (a*J H):=@commutative_ideal_mul G I hI a (J H) hInH.
have hRemainder:I (J r).
  have hDifference:=@commutative_ideal_add G I hI alpha (-(a*J H)) hAlpha
    (@commutative_ideal_opp G I hI _ hProduct).
  by rewrite hDivision addrAC subrr add0r in hDifference.
have hDivides:commutative_divides H r:=(hKernel r).1 hRemainder.
have hDomain:=@holomorphic_germ_no_zero_divisors R Z NZ hNZ 0.
have hZero:=@polynomial_bounded_divisible_zero A P embed variable coefficient hP hDomain H r k
  hDistinguished.1.1 hSupport hDivides.
exists a;split;first exact:hQuotient.
by rewrite hDivision hZero rmorph0 addr0.
Qed.
End PrefixKernel.
