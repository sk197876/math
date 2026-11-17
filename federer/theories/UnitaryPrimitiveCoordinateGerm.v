(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: the original primitive coordinate germ equals
    the conjugated original coordinate sum. Reuse actual coordinate
    representatives and the proved finite-sum germ equation. *)
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
Variables q h:U.
Variable m:'I_n.
Variable hMN:((m:nat)<=n)%N.
(** Source for [unitary_primitive_coordinate_germ]: the exact
    original inverse-coordinate germ identity, retaining the required
    complex conjugates, 3.4.12, p. 339. *)
Theorem unitary_primitive_coordinate_germ:
  (forall x:X,mapg q (mapg h x)=x) ->
  @holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m q ->
  P h (@HolomorphicCoordinateGerms.value R X NX hNX n e he omega m)=
  \sum_(i<n-m) (@HolomorphicScalars.map R X NX hNXR 0
    (ComplexScalarTheory.conjugate (omega (ordinal_coordinate_tail_index hMN i) (mapg q (e m)))))*
    (@HolomorphicCoordinateGerms.value R X NX hNX n e he omega (ordinal_coordinate_tail_index hMN i)).
Proof.
move=>hInverse hQ.
have [f hValues]:=@holomorphic_coordinate_representative_exists R X NX hNX n e he omega m.
have hGamma:=@HolomorphicCoordinateGerms.laws R X NX hNX n e he omega m f hValues.
have [g [hG hPullValues]]:=(@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR h) f.
rewrite hGamma in hG;rewrite hG.
apply:(@holomorphic_coordinate_linear_combination_germ R X NX hNX n e he omega
  [the finType of 'I_(n-m)] (ordinal_coordinate_tail_index hMN)
  (fun i=>ComplexScalarTheory.conjugate (omega (ordinal_coordinate_tail_index hMN i) (mapg q (e m)))) g)=>x.
rewrite hPullValues hValues.
exact:(@unitary_primitive_suffix_covector R X H hH n e he omega hDual hON q h hInverse m hMN hQ x).
Qed.
End Coordinates.
