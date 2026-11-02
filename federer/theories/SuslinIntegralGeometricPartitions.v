(** Supporting the projection slicing identities of Federer (1969), 2.10.16,
    p. 178: the exponent-one cost on Suslin sets is below the
    Borel-generator measure, and its shrinking-partition sums recover that
    measure. This extends the argument of 2.10.8–2.10.9, p. 175, using the
    proved Borel incidence hull. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions OrthogonalProjectionProbability ProjectionBeta
  ProjectedVolumeIncidence ProjectionIncidenceMeasure IntegralGeometricGauge
  MetricProductBackground MetricProductCompleteness MetricProductSeparability
  BorelRegularMeasureUP ProductMeasure ProductBorelRegularity
  SuslinSetUP SuslinPreimages BorelClosedProjection BorelImageMeasurability
  SuslinImageSeparation BorelSeparation TopologicalBorel BorelFamilyBasic BorelFunctionBasic
  TopologicalProductMaps MetricDiameter MetricDiameterClosure MeasureUP MeasureBasic IntegralGeometricCoverCosts IntegralGeometricMeasure
  BorelCoverCostUP BorelCaratheodoryMeasure MetricScaleEnvelope MetricScaleEnvelopeUP
  CaratheodoryLimitUP SuslinProjectionCostHull SuslinPartitionCostLimits
  ClosedCoverTreeUP CoverPartitionTreeUP ExtendedRealBoundsUP BorelPartitionCostLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.


(** Source for [suslin_integral_geometric_cost_bound]: supporting
    cost lower bound for 2.10.16, p. 178, from the
    countable-cover inequality of 2.10.9, p. 175. Borel
    generators cover a Suslin source; no Borel source is needed. *)
Lemma suslin_integral_geometric_cost_bound (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R A -> @integral_geometric_gauge R n m hmn 1 A<=
    @borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (@integral_geometric_gauge R n m hmn 1) A.
Proof.
move=> hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose J := @borel_metric_sets R X.
pose S := fun j : J => val j.
pose c := @integral_geometric_gauge R n m hmn 1.
pose d := fun j : J => c (val j).
pose nu := metric_scale_envelope S d 1.
have hn := @metric_scale_envelope_specification R X J S d 1.
have hlow : c A<=nu A.
  apply: (metric_scale_envelope_greatest hn)=> G hG _ hcov.
  apply: (@integral_geometric_gauge_countable_cover R n m hmn 1 J G S A (lexx _) hG hA _ hcov)=> j hj.
  exact: metric_borel_suslin (set_valP j).
apply: le_trans hlow _.
exact (@caratheodory_limit_upper R X J S d (borel_caratheodory_measure c)
  (borel_caratheodory_specification c) A 1 nu lte01 hn).
Qed.

(** Source for [suslin_integral_geometric_cost_hull]: supporting
    admissible Borel generator for 2.10.16, p. 178. The
    proved incidence hull has exactly the same exponent-one
    cost and does not enlarge diameter, also at infinite cost. *)
Lemma suslin_integral_geometric_cost_hull (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> exists C, borel_set C /\ S `<=` C /\
    extended_metric_diameter C<=extended_metric_diameter S /\
    @integral_geometric_gauge R n m hmn 1 C<=@integral_geometric_gauge R n m hmn 1 S.
Proof.
move=> hS; have [C hC] := suslin_projection_incidence_hull_exists hmn hS.
exists C; split; first exact hC.1.
split; first exact hC.2.1.
split; first exact hC.2.2.2.
by rewrite (projection_incidence_hull_gauge_one hS hC).
Qed.

(** Source for [suslin_integral_geometric_partition_supremum]:
    supporting Suslin partition identity for 2.10.16, p. 178,
    extending the argument of 2.10.8–2.10.9, p. 175,
    at exponent one, the only exponent used in slicing. *)
Theorem suslin_integral_geometric_partition_supremum (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n))) A :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_extended_real_supremum [set a | exists j,
    a=borel_partition_level_cost (@integral_geometric_gauge R n m hmn 1) P A j]
    (@integral_geometric_measure R n m hmn 1 A).
Proof.
move=> hE hP hA.
exact (@suslin_partition_cost_supremum R (inner_metric_space (@euclidean_inner_productP R n))
  (@integral_geometric_gauge R n m hmn 1)
  (@integral_geometric_gauge_borel_cover_cost R n m hmn 1 (lexx _))
  (@suslin_integral_geometric_cost_bound R n m hmn)
  (@suslin_integral_geometric_cost_hull R n m hmn) E P hE hP A hA).
Qed.
