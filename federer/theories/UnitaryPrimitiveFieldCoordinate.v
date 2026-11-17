(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: the exact inverse unitary coordinate gives the
    original primitive element in the quotient fraction field.
    Preserve the conjugated coefficients and original scalar triangles. *)
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
From Federer Require Import HolomorphicCoordinateGermsSealed HolomorphicCoordinateGermsExistence HolomorphicCoordinateLinearCombination HolomorphicGermRepresentatives HolomorphicScalarsSealed.
From Federer Require Import UnitarySuffixCovector.
From Federer Require Import HolomorphicCoordinateNorm FiniteCoordinates HolomorphicPrefixGermMap
  HolomorphicPrefixComplexScalars UnitaryPrimitiveCoordinateGerm CoefficientFractionFieldUP.
Section FieldCoordinate.
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
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Variable m:'I_n.
Variable hMN:((m:nat)<=n)%N.
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R
  (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Variable hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o (pi \o E)) _) eta phi.
Local Notation gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega).
Local Notation scalarPrefix:=(@HolomorphicScalars.map R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0).
Local Notation scalarAmbient:=(@HolomorphicScalars.map R X NX hNXR 0).
Variables q h:U.
(** Source for [unitary_primitive_field_coordinate]: the original
    primitive sum equals the actual inverse-rotated coordinate class,
    3.4.12, p. 339. *)
Theorem unitary_primitive_field_coordinate:
  (forall x:X,mapg q (mapg h x)=x) ->
  @holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m q ->
  inclusion (pi (P h (gamma m)))=
    \sum_(i<n-m) phi (eta (scalarPrefix
      (ComplexScalarTheory.conjugate (omega (ordinal_coordinate_tail_index hMN i) (mapg q (e m))))))*
      inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))).
Proof.
move=>hInverse hQ.
have hScalar c:phi (eta (scalarPrefix c))=inclusion (pi (scalarAmbient c)).
  rewrite (coefficient_fraction_scalar_triangle hCoefficient).
  change (inclusion (pi (E (scalarPrefix c)))=inclusion (pi (scalarAmbient c))).
  by rewrite holomorphic_prefix_complex_scalar_triangle.
have hGerm:=@unitary_primitive_coordinate_germ R X H hH n e he omega hDual hON q h m hMN hInverse hQ.
rewrite hGerm !rmorph_sum.
apply:eq_bigr=>i _;by rewrite !rmorphM hScalar.
Qed.
End FieldCoordinate.
