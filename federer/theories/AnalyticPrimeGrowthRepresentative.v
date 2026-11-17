(** Federer (1969), 3.4.8(13), pp. 328, 336:
    the actual prime variety growth representative in the
    original coordinates, obtained by the proved common-rotation
    construction and exact orthogonal transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticDepthReductionAlmost MappingMultiplicity EuclideanLebesgueDimensions CoordinateProjection
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  AnalyticPrefixCoordinatesSealed AnalyticPrimeModelCompactRepresentative AnalyticPrimeLocalModelUP
  Federer348PrimeReduction AnalyticReductionLociUP HaarConullRightSelection CoordinateProjectionRotation
  AnalyticRotatedVarietyRepresentative OrthogonalCoordinateModelTransport SetGermCoordinateImage
  AnalyticPrimeRotatedGrowthRepresentative OrthogonalGrowthRepresentativeTransport
  CommonCoordinateGrowthRepresentative UniformHausdorffGrowthUP RectifiableSetUP HausdorffMeasure
  ExteriorIndices FiniteAnalyticVarietyUP NormFiniteLinearBound NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrimeGrowth.
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
Variable I:set G.
Variables U H:set X.
Variable m:'I_n.
Local Notation hMN:=(ltnW (ltn_ord m)).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Local Notation om:=(@orthogonal_element_map R X B hB n e he).

(** Source for [analytic_prime_growth_representative]: the original
    positive-dimensional representative in 3.4.8(13),
    pp. 328, 336, with finite Hausdorff mass,
    actual germ equality and uniform all-subset diameter growth. *)
Theorem analytic_prime_growth_representative:
  U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
  I=ideal (@set_germ T 0 H) ->is_prime_commutative_ideal I ->
  (0<m)%N ->depth I=(m:nat) ->
  exists (S:set X) (b:R),
    @compact (inner_metric_space hB) S /\
    @set_germ T 0 S=@set_germ T 0 H /\
    @is_measure_m_rectifiable R (inner_metric_space hB)
      (@hausdorff_measure R (inner_metric_space hB) m) m S /\
    @is_uniform_hausdorff_growth R (inner_metric_space hB) m S b.
Proof.
move=>hU0 hH hIEquation hPrime hPositive hDepth.
have [g [S [b [hCompact [hGerm [hRect hGrowth]]]]]]:=
  @analytic_prime_rotated_growth_representative R n I U H m hU0 hH hIEquation hPrime hPositive hDepth.
have hTransport:=@orthogonal_growth_representative_transport R n m (hom_as_linear (om g)) S H b
  (orthogonal_element_orthogonal g) hCompact hGerm hRect hGrowth.
exists (om g @` S),b;exact:hTransport.
Qed.
End PrimeGrowth.
