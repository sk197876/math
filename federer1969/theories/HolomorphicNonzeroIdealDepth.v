(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    pp. 328–329: original A_p membership implies original B_p
    after Haar almost every original unitary prefix rotation. The
    actual positive jet, exact coordinate chart, sphere measure and
    arbitrary original Haar normalization are proved internally. *)
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
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import HolomorphicFullPrefixGermSubring UnitaryGroupInhabited HolomorphicReductionATailDepthDrop HolomorphicReductionHaarFibre AnalyticReductionDepthUP HolomorphicDepthSealed HolomorphicReductionTailPrefixStable UnitaryCoordinateFixingHaar MeasureAlmostPositiveWitness ComplexScalarLaws CommutativeIdealUP GrassmannAbbreviations EuclideanInnerProduct ComplexModulus ComplexScalarNorm ContinuousMultilinearSealed OrthonormalFamilies FiniteCoordinates HolomorphicCoordinateNorm
  StandardHermitianCoordinates ComplexEuclideanCoordinates HolomorphicGermJetsSealed HolomorphicGermFormsUP
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicReductionPrefixWitness
  HolomorphicGermCoordinateDirections HolomorphicPrefixSphereCoordinates HolomorphicReductionDirectionalTransport
  FieldPrefixCoordinatesSealed HolomorphicCoordinateSubringFamilyUP HolomorphicPrefixGermSubring
  MetricSubsetBackground HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic HaarIntegralUP
  UnitaryFixingSphereAction UnitaryFixingSphereHaarNull.
Section NonzeroDepth.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n.+1->X.
Variable he:is_basis e.
Variable omega:'I_n.+1->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].

Variable hON:orthonormal_family Herm e.
(** Source for [holomorphic_nonzero_proper_ideal_depth_lt]: a
    nonzero proper ideal has depth below the full complex
    dimension, extending 3.4.8(11), p. 333, under
    3.4.12, p. 339. The full prefix subring is
    the whole original germ ring; apply the proved A-tail drop. *)
Theorem holomorphic_nonzero_proper_ideal_depth_lt (I:set G):
  is_commutative_ideal I ->~I 1 ->(exists alpha,I alpha /\alpha<>0) ->
  (@HolomorphicDepth.value R X Herm hHerm n.+1 e he omega I<n.+1)%N.
Proof.
move=>hI hProper [alpha [hAlpha hNonzero]].
have [g _]:=@unitary_group_inhabited R X Herm hHerm (n.+1+n.+1) eR heR.
have hQ:=@holomorphic_full_prefix_germ_subring R X NX hNXR n.+1 e he omega hDual.
have hA:@holomorphic_reduction_actual_A R X Herm hHerm n.+1 e he omega I ord_max g.
  apply:(holomorphic_reduction_A_membership
    (@holomorphic_reduction_actual_laws R X Herm hHerm n.+1 e he omega I) ord_max g).2.
  split;first exact:ltn0Sn.
  pose M:=@holomorphic_unitary_germ_map R X Herm hHerm (n.+1+n.+1) eR heR g.
  exists (M alpha);split.
  - apply/holomorphic_rotated_germ_ideal_membership;by exists alpha.
  - split;first by rewrite hQ.
    move=>hZero;apply:hNonzero.
    apply:(@holomorphic_unitary_germ_map_injective R X Herm hHerm (n.+1+n.+1) eR heR g).
    by rewrite rmorph0.
have hEmptyTail:forall j:'I_n.+1,(n.+1<=j)%N ->
    @holomorphic_reduction_actual_B R X Herm hHerm n.+1 e he omega I j g.
  move=>j hj;exfalso;have hFalse:=leq_ltn_trans hj (ltn_ord j);by rewrite ltnn in hFalse.
have hIndex:(@Ordinal n.+2 n.+1 (ltn_ord (ord_max:'I_n.+1))) = ord_max by apply:val_inj.
rewrite -hIndex in hA.
exact:(@holomorphic_reduction_A_tail_depth_drop R X Herm hHerm n.+1 e he hON omega hDual
  I hI hProper ord_max g hEmptyTail hA).
Qed.
End NonzeroDepth.
