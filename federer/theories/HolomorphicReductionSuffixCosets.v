(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(9),
    p. 330: the original B-tail condition is constant on each
    original suffix unitary coset. Reuse the actual quotient-integrality
    theorem and its original monic directional witnesses. *)
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
From Federer Require Import UnitarySuffixCovector HolomorphicScalarsSealed
  HolomorphicReductionActual HolomorphicReductionOriginalFieldInputs HolomorphicIntegralRotationDirections
  CommutativeIdealUP CommutativeQuotientSealed TopologicalGroupLaws UnitaryGroupClosed.
Section Cosets.
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
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Variable m:'I_n.
Local Notation F:=(@holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m).
Local Notation Bj:=(@holomorphic_reduction_actual_B R X H hH n e he omega I).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.

Variables (mulF:F->F->F) (invF:F->F) (unitF:F).
Variable hF:is_subgroup_restriction mulU invU unitU F mulF invF unitF.
(** Source for [holomorphic_reduction_suffix_B_stable]: every
    original suffix rotation preserves all original B-tail tests;
    a proper ideal suffices, 3.4.12, p. 339. *)
Theorem holomorphic_reduction_suffix_B_stable (g:U) (q:F):
  (forall j:'I_n,(m<=j)%N ->Bj j g) ->
  forall j:'I_n,(m<=j)%N ->Bj j (mulU g (set_val q)).
Proof.
move=>hAllB.
pose hMN:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
pose Ig:=@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g.
have hIdeal:=@holomorphic_rotated_germ_ideal_is_ideal R X H hH (n+n) eR heR I g hI.
have hProperRot:=@holomorphic_rotated_germ_ideal_proper R X H hH (n+n) eR heR I g hProper.
pose complexG:=@HolomorphicScalars.map R X NX hNXR 0.
pose C:=@CommutativeIdealQuotient.space (ComplexScalars.C R) G complexG Ig hIdeal hProperRot.
pose pi:=@CommutativeIdealQuotient.projection (ComplexScalars.C R) G complexG Ig hIdeal hProperRot.
have hPi:=@CommutativeIdealQuotient.laws (ComplexScalars.C R) G complexG Ig hIdeal hProperRot.
have hIntegral:=@holomorphic_reduction_original_quotient_integral R X H hH n e he omega hDual
  I hI hProper g C pi hPi m hMN hAllB.
exact:(@holomorphic_integral_suffix_rotation_B R X H hH n e he omega hDual hON I g C pi hPi
  m hMN mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF hIntegral q).
Qed.
(** Source for [holomorphic_reduction_B_suffix_coset]: the literal
    original coset equivalence, with actual inverse rotations,
    3.4.12, p. 339. *)
Theorem holomorphic_reduction_B_suffix_coset (g:U) (q:F):
  (forall j:'I_n,(m<=j)%N ->Bj j (mulU g (set_val q))) <->
  (forall j:'I_n,(m<=j)%N ->Bj j g).
Proof.
split.
- move=>hAllB.
  have hRestored:=@holomorphic_reduction_suffix_B_stable (mulU g (set_val q)) (invF q) hAllB.
  have hLocal:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO U mulU invU unitU hU
    (@orthogonal_group_lch R XR B hB (n+n) eR heR mulO invO unitO hO)
    (@unitary_group_closed R X H hH (n+n) eR heR).
  have hGroup:=topological_group_laws (lch_group_topological hLocal).
  by rewrite (subgroup_restriction_inv hF) (@group_mulgK U mulU invU unitU hGroup (set_val q) g) in hRestored.
- exact:(@holomorphic_reduction_suffix_B_stable g q).
Qed.
End Cosets.
