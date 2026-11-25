(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 334:
    every original B_j witness supplies an
    actual prepared W_j equation in I_g.
    The original positive degree, vanishing lower
    coefficient values and holomorphic prefix domain
    are proved internally from the earlier preparation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct NormFiniteLinearBound HolomorphicUP OrthogonalGroupTopology HolomorphicGermUP
  HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicCoordinateGermsSealed FieldPrefixCoordinatesSealed
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicRotatedGermIdeal HolomorphicReductionActual
  CommutativeIdealUP CommutativePolynomialEvaluationUP CommutativePolynomialSealed CommutativePolynomialEvaluationSealed
  HolomorphicPrefixPreparedPolynomial DistinguishedHolomorphicPolynomialActualMonic PointedHolomorphicFunctionalGermExistence SetGermUP SetGermOrder HolomorphicGermVanishingSealed HolomorphicTriangularGermPoint HolomorphicAllDirectionsPointGerm HolomorphicGermVanishingIdeal HolomorphicIdealPropriety HolomorphicVarietyGermUP HolomorphicVarietyRepresentativeCentre HolomorphicDepthSealed AnalyticReductionDepthUP HolomorphicRotatedVanishingIdeal UnitaryComplexMapSealed UnitaryComplexInverse NormBoundedLinearTopology PointGermHomeomorphism SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroDepth.
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

Local Notation T:=(Topological.clone (real_norm_metric_space hNXR) _).
(** Source for [holomorphic_zero_depth_point_germ]: the full
    original depth-zero base, 3.4.8(11), p. 333, under
    3.4.12, p. 339. Original simultaneous directional witnesses
    supply the equations; the actual unitary inverse restores
    the original centre and set germ. *)
Theorem holomorphic_zero_depth_point_germ (alpha:@set_germ_space T 0):
  @is_holomorphic_variety_germ R X NX hNXR 0 alpha ->
  alpha<>@set_germ T 0 set0 ->
  @HolomorphicDepth.value R X Herm hHerm n e he omega
    (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha) = 0%N ->
  alpha = @set_germ T 0 [set 0].
Proof.
move=>hAlpha hNonempty hZeroDepth.
pose I:set G:=@HolomorphicSetIdeal.value R X NX hNXR 0 alpha.
have hI:=@holomorphic_set_ideal_ring_laws R X NX hNXR 0 alpha.
have hProper:~I 1.
  move=>hUnit;apply:hNonempty;exact:(holomorphic_set_ideal_contains_one alpha).1 hUnit.
have hDepth:=@HolomorphicDepth.laws R X Herm hHerm n e he omega I.
rewrite hZeroDepth in hDepth.
have [g hAll]:=analytic_reduction_depth_attained hDepth.
have [U [S [hU0 [hVariety hGerm]]]]:=hAlpha.
have hS0:S 0.
  apply:(@holomorphic_variety_representative_centre R X NX hNXR U S 0 hU0 hVariety).
  by rewrite hGerm.
pose u:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR g.
have [q [hLeft hRight]]:=@unitary_complex_inverse_exists R X Herm hHerm (n+n) eR heR g.
pose v:=@UnitaryComplexMap.value R X Herm hHerm (n+n) eR heR q.
have hVBound:=@norm_finite_linear_bounded R XR XR NX NX hNXR hNXR (n+n) eR heR (complex_hom_real v).
have hV:=@norm_bounded_linear_continuous R XR XR NX NX hNXR hNXR (complex_hom_real v) hVBound.
have hRotated:=@holomorphic_rotated_vanishing_ideal R X Herm hHerm (n+n) eR heR g S.
rewrite hGerm in hRotated.
have hPointPre:set_germ_subset (@set_germ T 0 (u @^-1` S)) (@set_germ T 0 [set 0]).
  apply:(@holomorphic_all_directions_point_germ R X Herm hHerm n e he omega hDual I g
    (@set_germ T 0 (u @^-1` S)) hI hProper).
  - move=>j;exact:hAll j (leq0n j).
  - rewrite hRotated;exact:subset_refl.
have hPoint:set_germ_subset (@set_germ T 0 S) (@set_germ T 0 [set 0]).
  exact:(@point_germ_inverse_transport T 0 u v S hV (linear0 u) (linear0 v) hRight hPointPre).
rewrite -hGerm;apply:set_germ_subset_antisymmetric;first exact:hPoint.
apply:set_germ_subset_from_sets=>x ->;exact:hS0.
Qed.
End ZeroDepth.
