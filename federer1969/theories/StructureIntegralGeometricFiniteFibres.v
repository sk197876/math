(** Federer (1969), 3.3.14, p. 298: finite original I-infinity
    mass gives almost-finite original fibres at almost every projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions
  OrthogonalProjectionProbability ProjectionBeta IntegralGeometricMeasure IntegralGeometricMultiplicity
  ProjectionMultiplicityIntegral NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm
  NonnegativeExtendedNormFiniteValues ClosedCoverTreeUP ClosedCoverTreeSealed
  CoverPartitionTreeUP CoverPartitionTreeSealed StructureProjectionConditions
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology PartialExtendedOrderLoci
  MappingMultiplicity CountingMeasure MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureUpperIntegralPositivePart MeasureAlmostUP MeasureAlmostBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_integral_geometric_finite_fibres]: supporting
    original condition (II) in Federer 3.3.14, p. 298. The actual
    shrinking-partition proof of 2.10.15 bounds the infinity norm of
    the ORIGINAL counting-integral profile by original I-infinity(E).
    All natural degrees remain, including zero: the underlying tree
    estimates need no positive-degree hypothesis. Actual finite upper
    counting integrals then make the ORIGINAL fibres finite almost
    everywhere. Every cover tree stays local. *)
Lemma structure_integral_geometric_finite_fibres (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  borel_set E ->@integral_geometric_measure R n m hmn +oo E< +oo ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|structure_projection_almost_finite_fibres E p].
Proof.
move=>hE hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=orthogonal_projection_metric_space R n m.
pose theta:=@orthogonal_projection_probability R n m hmn.
pose g:=@projection_multiplicity_integral R n m E.
have hTheta:=theta_star_is_measure R hmn.
have [D [hD hDense]]:=euclidean_metric_separable R n.
have hX:(@setT X)!=set0 by exists (0%R:X).
pose C:=@ClosedCoverTree.value R [the metricType R of X] D hD hDense hX.
pose B:=@CoverPartitionTree.value X C.
have hC:=@ClosedCoverTree.laws R [the metricType R of X] D hD hDense hX.
have hB:=@CoverPartitionTree.laws X C.
have hProfile:=@projection_multiplicity_tree_parameter_integral R n m hmn C B E hC hB hE.
have hBound:=@projection_multiplicity_tree_norm_bound R n m hmn C B E +oo hC hB hE (leey 1).
rewrite projection_beta_infinity mul1e in hBound.
have hNonnegative p:0<=g p:=@projection_multiplicity_integral_nonnegative R n m E p hE.
have hNorm:=@nonnegative_extended_exponent_norm_specification R P
  theta g +oo hTheta hNonnegative (leey 1) hProfile.1.
have hNormFinite:nonnegative_extended_exponent_norm theta g +oo< +oo:=le_lt_trans hBound hFinite.
have hValues:=@finite_nonnegative_extended_norm_almost_finite R P
  theta hTheta g +oo _ hNonnegative hNorm hNormFinite.
apply:(measure_almost_everywhere_mono hTheta _ hValues)=>p hp.
pose L:=@euclidean_lebesgue_measure R m.
have hL:=euclidean_lebesgue_is_measure R m.
have hIntegral:=@projection_multiplicity_integral_specification R n m E p hE.
change (is_true (g p \is a fin_num)) in hp.
have hpFinite:g p< +oo by move:hp; rewrite (ge0_fin_numE (hNonnegative p)).
have hUpper:measure_upper_integral L (projection_multiplicity_integrand E p)< +oo.
  have hEqual:=measure_upper_integral_unique
    (measure_upper_integral_specification L (projection_multiplicity_integrand E p)) hIntegral.2.1.
  rewrite hEqual; exact:hpFinite.
have hCounts:=(@measure_finite_upper_integral_consequences R [the choiceType of Y]
  L hL (projection_multiplicity_integrand E p) hUpper).2.
apply:(measure_almost_everywhere_mono hL _ hCounts)=>y [v [hv hBelow]].
have hValue:@mapping_multiplicity R [the choiceType of X] Y
  (euclidean_projection_linear p) E y=v:=hv.
apply:contrapT=>hInfinite.
have hCount:=@counting_measure_infinite R [the choiceType of X]
  (mapping_fibre (euclidean_projection_linear p) E y) hInfinite.
rewrite /mapping_multiplicity hCount in hValue.
by rewrite -hValue ltxx in hBelow.
Qed.
