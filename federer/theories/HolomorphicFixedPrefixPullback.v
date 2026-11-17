(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: the actual suffix rotations fix every original
    prefix coefficient germ. Use the original coordinate square
    and the proved pointed pullback composition. *)
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
From Federer Require Import FiniteCoordinates FieldPrefixCoordinatesSealed FieldPrefixCoordinatesUP
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicCoordinateNorm
  PointedHolomorphicPullbackComposition UnitarySuffixCovector.
Section Coordinates.
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
Variable m:nat.
Variable q:U.
Variable hQ:@holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m q.
(** Source for [holomorphic_fixed_prefix_projection]: the original
    p_m q equals p_m, 3.4.12, p. 339. *)
Lemma holomorphic_fixed_prefix_projection (hMN:(m<=n)%N)
    (projection:Hom X (coordinate_space (ComplexScalars.C R) m)):
  is_field_prefix_projection omega hMN projection ->forall x,projection (mapg q x)=projection x.
Proof.
move=>hProjection x;apply/ffunP=>i;rewrite !hProjection.
exact:(@unitary_fixed_prefix_covector R X H hH n e he omega hDual hON q m hQ
  (widen_ord hMN i) (ltn_ord i) x).
Qed.
(** Source for [holomorphic_fixed_prefix_germ]: original prefix
    coefficient germs are fixed by the actual suffix pullback,
    3.4.12, p. 339. *)
Theorem holomorphic_fixed_prefix_germ (hMN:(m<=n)%N):
  forall alpha,P q (@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN alpha)=
    @holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN alpha.
Proof.
pose projection:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m hMN.
pose E:=@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN.
have hProjection:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega m hMN.
have hE:=@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega m hMN.
have hQG:=@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR q.
have hComposition:=pointed_holomorphic_pullback_composes hQG hE.
apply:(pointed_holomorphic_pullback_map_extensional hComposition hE).
exact:(holomorphic_fixed_prefix_projection hProjection).
Qed.
End Coordinates.
