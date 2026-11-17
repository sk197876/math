(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 334:
    every original B_j witness supplies an
    actual prepared W_j equation in I_g.
    The original positive degree, vanishing lower
    coefficient values and holomorphic prefix domain
    are proved internally from the earlier preparation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import SetGermUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct NormFiniteLinearBound HolomorphicUP OrthogonalGroupTopology HolomorphicGermUP
  HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicCoordinateGermsSealed FieldPrefixCoordinatesSealed
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicRotatedGermIdeal HolomorphicReductionActual
  CommutativeIdealUP CommutativePolynomialEvaluationUP CommutativePolynomialSealed CommutativePolynomialEvaluationSealed
  HolomorphicPrefixPreparedPolynomial DistinguishedHolomorphicPolynomialActualMonic PointedHolomorphicFunctionalGermExistence HolomorphicCoordinateSubringFamilySealed OrthonormalFamilies HolomorphicExceptionalIdealDepth HolomorphicIdealDepthMonotonicity HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyVanishingLaws HolomorphicIdealPropriety HolomorphicGermVanishingSealed HolomorphicDepthSealed UnitaryGroupHaar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EnlargedDepth.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].

Variable hON:orthonormal_family Herm e.
Local Notation T:=(Topological.clone (real_norm_metric_space hNXR) _).
(** Source for [holomorphic_enlarged_ideal_variety_depth_drop]: the
    original enlarged exceptional variety is empty or has depth
    below m, extending 3.4.8(11), p. 334, under
    3.4.12, p. 339. All original unitary group operations
    are chosen internally, and the possible unit ideal remains. *)
Theorem holomorphic_enlarged_ideal_variety_depth_drop (I K:set G)
    (hK:is_finitely_generated_commutative_ideal K)
    (g:@unitary_group R X Herm hHerm (n+n) eR heR) (m:'I_n):
  (0<m)%N ->
  @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g `<=` K ->
  (forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g) ->
  (exists beta,K beta /\@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega m beta /\beta<>0) ->
  let alpha:=@HolomorphicIdealVarietyGerm.value R X NX hNXR 0 K hK in
  alpha = @set_germ T 0 set0 \/
  (@HolomorphicDepth.value R X Herm hHerm n e he omega
    (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha)<m)%N.
Proof.
move=>hPositive hIK hTail hIntersection alpha.
have [F hGenerated]:=hK.
have hKIdeal:=generated_commutative_ideal_laws hGenerated.
case:(pselect (K 1))=>hUnit.
- left;apply:(@holomorphic_set_ideal_contains_one R X NX hNXR 0 alpha).1.
  exact:(@HolomorphicIdealVarietyVanishingLaws.ideal_in_vanishing_ideal_of_variety R X NX hNXR 0 K hK 1 hUnit).
- right.
  have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal hHaar]]]]]]]]]:=
    @unitary_group_haar_exists R X Herm hHerm (n+n) eR heR.
  have hDrop:=@holomorphic_exceptional_ideal_depth_drop R X Herm hHerm n e he
    mulO invO unitO hO mulU invU unitU hU omega hON hDual I K g m
    hPositive hKIdeal hUnit hIK hTail hIntersection.
  have hBound:=@holomorphic_ideal_depth_antitone R X Herm hHerm n e he omega K
    (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha)
    (@HolomorphicIdealVarietyVanishingLaws.ideal_in_vanishing_ideal_of_variety R X NX hNXR 0 K hK).
  exact:leq_ltn_trans hBound hDrop.
Qed.
End EnlargedDepth.
