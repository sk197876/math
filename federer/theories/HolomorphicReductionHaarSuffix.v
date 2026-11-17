(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 326, 329–330: every original prime ideal and original
    B-tail point gives C_m and the complete B-tail for almost
    every actual suffix unitary rotation. All quotient and fraction
    objects are local witnesses supplied by the existing opaque interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicGermFormsSealed HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition PointedHolomorphicLinearPullbackForms
  HolomorphicCoordinateSubringFamilySealed UnitaryCoordinateFixing HolomorphicUnitaryPrefixInvariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import TopologicalGroupLaws UnitaryGroupClosed.
From Federer Require Import OrthonormalFamilies Bilinear TensorUP ComplexScalarLaws HermitianComplexLinearity HermitianBasisCoordinates UnitaryHermitianPreservation OrdinalCoordinateTail OrdinalCoordinateTailSum Annihilator FiniteDualDimension DualityAnnihilator.
Import ComplexScalarTheory.
From Federer Require Import UnitarySuffixCovector FiniteCoordinates HolomorphicCoordinateNorm
  HolomorphicScalarsSealed HolomorphicCoordinateGermsSealed HolomorphicPrefixGermMap
  HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicRotatedIdealPrime
  HolomorphicReductionOriginalFieldInputs HolomorphicReductionPrimitiveHaar HolomorphicPrimitiveRotationRelations
  HolomorphicIntegralRotationDirections CommutativeIdealUP CommutativeSubringUP
  CommutativeQuotientSealed CommutativeQuotientLaws FractionFieldSealed CoefficientFractionFieldSealed
  HaarIntegralUP MeasureUP MeasureAlmostBasic.
Section OriginalSuffix.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable hON:orthonormal_family H e.
Variable I:set G.
Variable g:U.
Variable m:'I_n.
Local Notation F:=(@holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m).
Local Notation Cm:=(@holomorphic_reduction_actual_C R X H hH n e he omega I m).
Local Notation Bj:=(@holomorphic_reduction_actual_B R X H hH n e he omega I).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.

Variables (mulF:F->F->F) (invF:F->F) (unitF:F).
Variable hF:is_subgroup_restriction mulU invU unitU F mulF invF unitF.
(** Source for [holomorphic_reduction_suffix_haar_almost_C_B]: the
    complete original complex counterpart of 3.4.8(8), with every
    original denominator and all original directional tests,
    3.4.12, p. 339. No finite-extension conclusion is assumed. *)
Theorem holomorphic_reduction_suffix_haar_almost_C_B (mu:set F->\bar R):
  is_prime_commutative_ideal I ->
  (forall j:'I_n,(m<=j)%N ->Bj j g) ->is_left_haar_measure mulF mu ->
  mu [set q:F|~(Cm (mulU g (set_val q)) /\
    forall j:'I_n,(m<=j)%N ->Bj j (mulU g (set_val q)))]=0%:E.
Proof.
move=>hPrime hAllB hMu.
pose hMN:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
pose Ig:=@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g.
have hPrimeRot:=@holomorphic_rotated_germ_ideal_prime R X H hH (n+n) eR heR I g hPrime.
pose complexG:=@HolomorphicScalars.map R X NX hNXR 0.
pose C:=@CommutativeIdealQuotient.space (ComplexScalars.C R) G complexG Ig hPrimeRot.1 hPrimeRot.2.1.
pose pi:=@CommutativeIdealQuotient.projection (ComplexScalars.C R) G complexG Ig hPrimeRot.1 hPrimeRot.2.1.
have hPi:=@CommutativeIdealQuotient.laws (ComplexScalars.C R) G complexG Ig hPrimeRot.1 hPrimeRot.2.1.
have hDomain:=@prime_commutative_quotient_domain G C Ig pi hPi hPrimeRot.
pose L:=@FractionField.space C hDomain.
pose inclusion:=@FractionField.embed C hDomain.
have hFraction:=@FractionField.laws C hDomain.
pose A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
pose E:=@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN.
pose scalar:{rmorphism A->C}:=GRing.RMorphism.clone A C (pi \o E) _.
pose original:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose M:=@CoefficientFractionField.space A L original.
pose eta:=@CoefficientFractionField.scalar A L original.
pose phi:=@CoefficientFractionField.inclusion A L original.
have hCoefficient:=@CoefficientFractionField.laws A L original.
have hPrimitiveNull:=@holomorphic_reduction_original_primitive_haar_null R X H hH n e he omega hDual hON
  I hPrime.1 hPrime.2.1 g C pi hPi L M inclusion hFraction m hMN hAllB eta phi hCoefficient
  mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF mu hMu.
have hIntegral:=@holomorphic_reduction_original_quotient_integral R X H hH n e he omega hDual
  I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB.
pose bad:=fun q:F=>~(Cm (mulU g (set_val q)) /\
  forall j:'I_n,(m<=j)%N ->Bj j (mulU g (set_val q))).
pose primitiveBad:=fun q:F=>~is_generated_commutative_subring
  (fun y:L=>y=inclusion (pi (@holomorphic_unitary_germ_map R X H hH (n+n) eR heR
    (invU (set_val q)) (@HolomorphicCoordinateGerms.value R X NX hNX n e he omega m))) \/
    exists a:M,y=phi a) setT.
have hSubset:bad `<=` primitiveBad.
  move=>q hBad hGenerated;apply:hBad;split.
  - exact:(@holomorphic_reduction_primitive_rotation_C R X H hH n e he omega hDual hON I g C pi hPi
      L M inclusion hFraction m hMN eta phi hCoefficient mulO invO unitO hO
      mulU invU unitU hU mulF invF unitF hF q hGenerated).
  - move=>j hMJ.
    exact:(@holomorphic_integral_suffix_rotation_B R X H hH n e he omega hDual hON I g C pi hPi
      m hMN mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF hIntegral q j hMJ).
have [lambda [hLambda hMeasure hRep hRegular]]:=hMu.
exact:(@measure_null_subset R (Choice.clone F _) mu hMeasure bad primitiveBad hSubset hPrimitiveNull).
Qed.
End OriginalSuffix.
