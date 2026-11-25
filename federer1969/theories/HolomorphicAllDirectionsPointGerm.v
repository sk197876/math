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
  HolomorphicPrefixPreparedPolynomial DistinguishedHolomorphicPolynomialActualMonic PointedHolomorphicFunctionalGermExistence SetGermUP SetGermOrder HolomorphicGermVanishingSealed HolomorphicTriangularGermPoint HolomorphicReductionPreparedEquation HolomorphicTriangularEquationDataUP HolomorphicPreparedTriangularEquation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AllDirections.
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
Variable I:set G.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.

Variable sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNXR) _) 0.
(** Source for [holomorphic_all_directions_point_germ]: the original
    simultaneous B_j hypotheses give all actual monic equations,
    extending the depth-zero argument of 3.4.8(11), p. 333,
    under 3.4.12, p. 339. No isolated-zero premise is added. *)
Theorem holomorphic_all_directions_point_germ:
  is_commutative_ideal I ->~I 1 ->
  (forall j,@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g) ->
  @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g `<=`
    @HolomorphicSetIdeal.value R X NX hNXR 0 sigma ->
  set_germ_subset sigma (@set_germ (Topological.clone (real_norm_metric_space hNXR) _) 0 [set 0]).
Proof.
move=>hI hProper hAllB hVanishing.
pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
pose data:=fun j:'I_n=>projT1 (cid (@holomorphic_prepared_triangular_equation_exists R X Herm hHerm n e he omega hDual I g j hI hProper (hAllB j))).
pose k:=fun j:'I_n=>holomorphic_triangular_degree (data j).
pose b:=fun j:'I_n=>@holomorphic_triangular_coefficients R X NX hNXR n omega Ig j (data j).
pose f:=fun j:'I_n=>@holomorphic_triangular_function R X NX hNXR n omega Ig j (data j).
have hLaws j:=@holomorphic_triangular_laws R X NX hNXR n omega Ig j (data j).
pose hJN:=fun j:'I_n=>leq_trans (leqnSn (j:nat)) (ltn_ord j).
pose P:=fun j:'I_n=>@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega j (hJN j).
apply:(@holomorphic_triangular_germ_point R X NX hNXR n e he omega hDual hJN P k
  b f sigma).
- move=>j;exact:FieldPrefixCoordinates.projection_laws.
- move=>j;exact:(hLaws j).1.
- move=>j i;exact:(hLaws j).2.1 i.
- move=>j x;exact:(hLaws j).2.2.2 x.
- move=>j;apply:hVanishing;exact:(hLaws j).2.2.1.
Qed.
End AllDirections.
