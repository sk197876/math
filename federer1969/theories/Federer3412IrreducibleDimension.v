(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), pp. 335–336:
    a positive original E_m reduction of an irreducible
    variety has m equal to its actual ideal depth.
    Apply the proved model (10), upper-null representative
    from (11), and positive measure of every nonempty
    m-dimensional holomorphic manifold germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import HolomorphicDepthReductionAlmost HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime HolomorphicVarietyGermDimensionSealed HolomorphicVarietyGermDimensionLaws HolomorphicGrowthRepresentative UniformHausdorffGrowthUP UniformHausdorffGrowthSupremum MetricDiameter ExtendedRealBounds RectifiableSetUP HausdorffMeasure UnitaryGroupClosed TopologicalGroupLaws HolomorphicReductionIndexDimension HolomorphicReductionAlmostCover HaarIntegralUP CompactGroupHaarNormalisation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HolomorphicPrimeReductionDimension HolomorphicLastReductionDepth StandardHermitianBasisValues UnitaryGroupHaar UnitaryComplexMapSealed HolomorphicRotatedCompositionInverse FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric
  HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  HolomorphicGermRing CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBooleanOrder
  HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyGermExistence
  HolomorphicReductionActual HolomorphicReductionLociUP AnalyticReductionDepthUP HolomorphicDepthSealed
  HolomorphicRotatedGermIdeal HolomorphicRotatedIdealDepth HolomorphicRotatedIdealRecovery
  HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelLaws Federer3412PrimeReduction
  FunctionalHolomorphicManifold HolomorphicGermHigherDegreeNull HolomorphicSubmanifoldGermNonNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalIrreducibleDimension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).



Variable alpha:@set_germ_space T 0.
Hypothesis hIrreducible:@is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 alpha.
Local Notation I:=(ideal alpha).
Local Notation d:=(@HolomorphicVarietyGermDimension.value R X Herm hHerm n e he omega alpha hIrreducible.1.1 hIrreducible.2).
Local Notation Em:=(@holomorphic_reduction_actual_E R X Herm hHerm n e he omega I).
Local Notation EC:=(inner_metric_space hB).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Orth:=(@orthogonal_group R XR B hB (n+n) eR heR).
Variables (mulO:Orth->Orth->Orth) (invO:Orth->Orth) (unitO:Orth).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR)
  Orth mulO invO unitO.
Variables (mulU:O->O->O) (invU:O->O) (unitU:O).
Hypothesis hU:is_subgroup_restriction mulO invO unitO O mulU invU unitU.

(** Source for [federer_3_4_12_13]: every original irreducible
    dimension and Haar assertion of 3.4.8(13), pp. 328,
    335–336, with the exact doubled measure degree required
    in 3.4.12, p. 339. The compact representative has
    finite H^(2m) mass and the literal finite supremum over
    all its nonempty subsets. Both dimension endpoints remain. *)
Theorem federer_3_4_12_13 (theta:set O->\bar R):
  is_normalised_haar_measure mulU theta ->
  (forall m:'I_n.+1,(exists g,Em m g)<->d=(m:nat)) /\
  (forall m:'I_n.+1,d=(m:nat) ->measure_almost_everywhere theta (Em m)) /\
  exists (S:set X) (c:R),
    @compact EC S /\@set_germ T 0 S=alpha /\
    @is_measure_m_rectifiable R EC (@hausdorff_measure R EC (d+d)) (d+d) S /\
    @is_uniform_hausdorff_growth R EC (d+d) S c /\
    (extended_real_sup [set q: \bar R |exists A:set X,A !=set0 /\A `<=` S /\
      q=(@hausdorff_measure R EC (d+d) A/
        (@extended_metric_diameter R EC A)^+(d+d))%E]< +oo)%E.
Proof.
move=>hTheta.
have hDimension:=@holomorphic_variety_germ_dimension_depth R X Herm hHerm n e he omega alpha
  hIrreducible.1.1 hIrreducible.2.
have hPrime:=(@holomorphic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hIrreducible.1.1).1 hIrreducible.
have hVanishing:exists sigma:@set_germ_space T 0,I=ideal sigma by exists alpha.
split.
- move=>m;rewrite hDimension.
  exact:(@holomorphic_reduction_nonempty_dimension_criterion R n I hPrime hVanishing
    mulO invO unitO hO mulU invU unitU hU m).
split.
- move=>m hM;apply:(@holomorphic_depth_reduction_haar_almost R n I hPrime hVanishing
    mulO invO unitO hO mulU invU unitU hU m theta).
  + by rewrite -hDimension.
  + exact:hTheta.
- have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=
    @holomorphic_growth_representative R n alpha hIrreducible.1.1 hIrreducible.2.
  exists S,c;split;first exact:hCompact.
  split;first exact:hGerm.
  rewrite hDimension.
  split;first exact:hRect.
  split;first exact:hGrowth.
  exact:uniform_hausdorff_growth_ratio_supremum hGrowth.
Qed.
End OriginalIrreducibleDimension.
