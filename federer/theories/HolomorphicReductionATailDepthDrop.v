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
From Federer Require Import HolomorphicReductionHaarFibre AnalyticReductionDepthUP HolomorphicDepthSealed HolomorphicReductionTailPrefixStable UnitaryCoordinateFixingHaar MeasureAlmostPositiveWitness ComplexScalarLaws CommutativeIdealUP GrassmannAbbreviations EuclideanInnerProduct ComplexModulus ComplexScalarNorm ContinuousMultilinearSealed OrthonormalFamilies FiniteCoordinates HolomorphicCoordinateNorm
  StandardHermitianCoordinates ComplexEuclideanCoordinates HolomorphicGermJetsSealed HolomorphicGermFormsUP
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicReductionPrefixWitness
  HolomorphicGermCoordinateDirections HolomorphicPrefixSphereCoordinates HolomorphicReductionDirectionalTransport
  FieldPrefixCoordinatesSealed HolomorphicCoordinateSubringFamilyUP HolomorphicPrefixGermSubring
  MetricSubsetBackground HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic HaarIntegralUP
  UnitaryFixingSphereAction UnitaryFixingSphereHaarNull.
Section Fibre.
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
Variable hON:orthonormal_family H e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable I:set G.
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Variable j:'I_n.
Local Notation p:=((j:nat).+1).
Local Notation hPN:=(ltn_ord j).
Local Notation aIndex:=(@Ordinal n.+1 p (ltn_ord j)).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) p).
Local Notation NY:=(@holomorphic_coordinate_norm R p).
Local Notation hNY:=(@holomorphic_coordinate_norm_laws R p).
Local Notation hNYR:=(complex_norm_real hNY).
Local Notation projection:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega p hPN).
Local Notation inclusion:=(@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X n e p hPN).
Local Notation hProjection:=(@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega p hPN).
Local Notation hInclusion:=(@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X n e p hPN).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega p hPN).
Local Notation J:=([set i:'I_n|(p<=i)%N]).
Local Notation F:=(@holomorphic_prefix_rotation_group R X H hH (n+n) eR heR n e p).
Local Notation sphere:=(@unitary_fixing_sphere R X H hH n e J).
Local Notation MS:=([the metricType R of metric_subset sphere]).
Local Notation SR:=(@holomorphic_prefix_real_sphere_inclusion R X p inclusion).
Local Notation PR:=(@holomorphic_prefix_real_sphere_projection R X p projection).

(** Source for [holomorphic_reduction_A_tail_depth_drop]: the
    actual original A_m and later B_j witnesses lower depth,
    extending 3.4.8(11), p. 334, under 3.4.12, p. 339.
    Apply the proved unitary Haar-fibre theorem and retain every
    later witness through the existing prefix transport. *)
Theorem holomorphic_reduction_A_tail_depth_drop (g:U):
  (forall k:'I_n,(p<=k)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega I k g) ->
  @holomorphic_reduction_actual_A R X H hH n e he omega I aIndex g ->
  (@HolomorphicDepth.value R X H hH n e he omega I<p)%N.
Proof.
move=>hLater hA.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocalU
  [mulF [invF [unitF [hF [hLocalF [mu hMu]]]]]]]]]]]]]]]:=
  @unitary_coordinate_fixing_haar_exists R X H hH (n+n) eR heR n e J.
have hAlmost:=@holomorphic_reduction_haar_fibre_almost_B R X H hH n e he hON omega hDual
  I hI hProper j mulO invO unitO hO mulU invU unitU hU mulF invF unitF hF mu g hMu.1 hA.
have [lambda [hLambda hMeasure hRest]]:=hMu.1.
have hMass:mu setT<>0%E.
  rewrite hMu.2;move=>hEqual.
  have hOne:(1:R) = 0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [h [_ hBj]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
have hLaterRot:=@holomorphic_reduction_tail_prefix_stable R X H hH n e he omega hDual I
  mulO invO unitO hO mulU invU unitU hU p g (set_val h) (set_valP h) hLater.
have hTail:has_analytic_reduction_tail
    (@holomorphic_reduction_actual_B R X H hH n e he omega I) j.
  exists (mulU g (set_val h))=>k hJK.
  case:(eqVneq k j)=>hEqual;first by rewrite hEqual.
  apply:hLaterRot.
  have hDifferent:(j:nat)!=k.
    apply/eqP=>hValues;apply:(negP hEqual);apply/eqP;apply:val_inj;exact:esym hValues.
  by rewrite ltn_neqAle hDifferent hJK.
have hMinimal:=analytic_reduction_depth_minimal
  (@HolomorphicDepth.laws R X H hH n e he omega I) hTail.
by rewrite ltnS.
Qed.
End Fibre.
