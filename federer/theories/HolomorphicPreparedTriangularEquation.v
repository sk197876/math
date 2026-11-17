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
  HolomorphicPrefixPreparedPolynomial DistinguishedHolomorphicPolynomialActualMonic PointedHolomorphicFunctionalGermExistence HolomorphicTriangularEquationDataUP HolomorphicReductionPreparedEquation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TriangularData.
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
Variable j:'I_n.
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) j).
Local Notation NY:=(@holomorphic_coordinate_norm R j).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R j)).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat) hJN).


(** Source for [holomorphic_prepared_triangular_equation_exists]: each
    original B_j witness gives the independent prepared equation
    data, extending 3.4.8(11), p. 333, under
    3.4.12, p. 339. Use the existing actual preparation;
    the selected data remains a local existence witness. *)
Theorem holomorphic_prepared_triangular_equation_exists:
  is_commutative_ideal I ->~I 1 ->
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g ->
  exists d:@holomorphic_triangular_equation_data R X NX hNXR n omega
    (@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g) j,True.
Proof.
move=>hI hProper hBj.
have [k [U [b [f [hK [hU0 [hUOpen [hHolomorphic [hZero [hMember hValues]]]]]]]]]]:=
  @holomorphic_reduction_prepared_equation R X Herm hHerm n e he omega hDual I g j hI hProper hBj.
have hLaws:(0<k)%N /\(forall i,holomorphic_representative_value (b i) 0 = 0) /\
    @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (holomorphic_germ f) /\
    forall x,holomorphic_representative_value f x = (omega j x)^+k+
      \sum_(i<k) holomorphic_representative_value (b i) (P x)*(omega j x)^+(i:nat).
  by split;last split;last split.
exists (@Build_holomorphic_triangular_equation_data R X NX hNXR n omega
  (@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g) j k
  (fun i=>holomorphic_representative_value (b i)) f hLaws).
exact:Logic.I.
Qed.
End TriangularData.
