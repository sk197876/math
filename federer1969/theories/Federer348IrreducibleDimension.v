(** Federer (1969), 3.4.8(13), pp. 328, 335–336:
    complete original irreducible dimension, Haar reduction and
    finite Hausdorff rectifiability theorem. The original dimension
    and measures are the existing opaque public objects. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  AnalyticDepthReductionAlmost AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime
  AnalyticVarietyGermUP AnalyticVarietyGermDimensionUP AnalyticVarietyGermDimensionSealed
  AnalyticVarietyGermDimensionLaws AnalyticIrreducibleGrowthRepresentative RectifiableSetUP
  HausdorffMeasure MetricDiameter ExtendedRealBounds UniformHausdorffGrowthUP UniformHausdorffGrowthSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalIrreducibleDimension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
Variable alpha:@set_germ_space T 0.
Hypothesis hIrreducible:@is_nonempty_irreducible_analytic_germ R X NX hNX 0 alpha.
Local Notation I:=(ideal alpha).
Local Notation d:=(@AnalyticVarietyGermDimension.value R X B hB n e he omega alpha hIrreducible.1.1 hIrreducible.2).
Local Notation Em:=(@analytic_reduction_actual_E R X B hB n e he omega I).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.

(** Source for [federer_3_4_8_13]: every assertion of original
    3.4.8(13), p. 328, proved on pp. 335–336.
    E_m is nonempty exactly at dim alpha; the
    dimension-index locus is Haar conull. An actual compact
    representative is (H^m,m) rectifiable and has the
    printed finite supremum over all nonempty subsets.
    The all-subset growth coefficient is retained as a
    stronger public conclusion, including both dimension endpoints. *)
Theorem federer_3_4_8_13 (theta:set O->\bar R):
  is_normalised_haar_measure mulO theta ->
  (forall m:'I_n.+1,(exists g,Em m g)<->d=(m:nat)) /\
  (forall m:'I_n.+1,d=(m:nat) ->measure_almost_everywhere theta (Em m)) /\
  exists (S:set X) (c:R),
    @compact (inner_metric_space hB) S /\@set_germ T 0 S=alpha /\
    @is_measure_m_rectifiable R (inner_metric_space hB)
      (@hausdorff_measure R (inner_metric_space hB) d) d S /\
    @is_uniform_hausdorff_growth R (inner_metric_space hB) d S c /\
    (extended_real_sup [set q: \bar R|exists A:set X,A !=set0 /\A `<=` S /\
      q=(@hausdorff_measure R (inner_metric_space hB) d A/
        (@extended_metric_diameter R (inner_metric_space hB) A)^+d)%E]< +oo)%E.
Proof.
move=>hTheta.
have hDimension:=@analytic_variety_germ_dimension_depth R X B hB n e he omega alpha
  hIrreducible.1.1 hIrreducible.2.
have hPrime:=(@analytic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hIrreducible.1.1).1 hIrreducible.
have hVanishing:exists sigma:@set_germ_space T 0,I=ideal sigma by exists alpha.
split.
- move=>m;rewrite hDimension.
  exact:(@analytic_reduction_nonempty_dimension_criterion R n I hPrime hVanishing mulO invO unitO hO m).
split.
- move=>m hM;apply:(@analytic_depth_reduction_haar_almost R n I hPrime hVanishing mulO invO unitO hO m theta).
  + by rewrite -hDimension.
  + exact:hTheta.
- have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=@analytic_irreducible_growth_representative R n alpha hIrreducible.
  exists S,c;split;first exact:hCompact.
  split;first exact:hGerm.
  rewrite hDimension.
  split;first exact:hRect.
  split;first exact:hGrowth.
  exact:uniform_hausdorff_growth_ratio_supremum hGrowth.
Qed.
End OriginalIrreducibleDimension.
