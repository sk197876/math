(** Supporting the slicing formulas of Federer (1969), 2.10.16, p. 178:
    projected-volume partition sums for Suslin source images, extending the
    Borel-source argument in 2.10.15, p. 178. The actual definitions are
    reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanLebesgueDimensions ProjectedVolumeMeasurability
  OrthogonalProjectionProbability ProjectionBeta ProjectionIncidenceMeasure
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  NonnegativeExtendedExponentNorm ProbabilityExtendedNormCover
  ProjectionMultiplicityIntegral TotalIncreasingIntegralValues
  ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic ShrinkingBorelPartitionLevels
  PartitionHitCounts PartitionCountingLimit PartitionImageIntegral MappingMultiplicity CountingMeasure
  BorelPartitionCostLimits BorelImageCoverCost TopologicalBorel BorelFamilyBasic BorelClosedProjection
  MeasureUP MeasureBasic MeasureIntegralUP TotalCountableNonnegativeIntegral
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale
  ProjectionMultiplicityPartitions SuslinProjectionMultiplicity SuslinMultiplicityIntegral
  SuslinPartitionCostLimits SuslinSetUP SuslinMeasurability BorelImageMeasurability
  BorelRegularMeasureUP EuclideanMetricCompleteness EuclideanMetricSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_suslin_partition_volume_sum_integral]:
    supporting Suslin-source countable integral sum for
    2.10.16, p. 178,
    using 2.4.8, p. 84. The previously proved Fubini
    formula for each projected volume gives the actual theta-star
    integral, hence measurability of every partition sum. *)
Lemma projection_suslin_partition_volume_sum_integral (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_partition_volume_sum (m:=m) P A j))
    (borel_partition_level_cost (@projected_incidence_measure R n m hmn) P A j).
Proof.
move=> hE hP hA.
have hS s : is_suslin_set R (A `&` P s) :=
  @suslin_partition_cell R (inner_metric_space (@euclidean_inner_productP R n)) E P hE hP A s hA.
apply: (@total_countable_nonnegative_integral R (orthogonal_projection_metric_space R n m)
  [the choiceType of (seq nat : Type)] (@orthogonal_projection_probability R n m hmn)
  (@theta_star_is_measure R n m hmn) [set s | size s=j]
  (fun s => projected_volume_function (m:=m) (A `&` P s))
  (@projected_incidence_measure R n m hmn \o (fun s => A `&` P s))
  (cover_partition_level_countable j)).
- move=> s hs p; exact: projected_volume_function_nonnegative.
- move=> s hs; apply: projected_volume_incidence_integral; exact: hS s.
Qed.

(** Source for [projection_suslin_partition_volume_sum_increases]:
    supporting Suslin-source increasing convergence to g(p) in the first proof
    display of 2.10.15, p. 178. Apply 2.4.7, p. 84,
    to the partition fibre counts of 2.10.10, p. 176,
    with their independently proved actual Lebesgue integrals. *)
Theorem projection_suslin_partition_volume_sum_increases (R : realType) (n m : nat)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  extended_increases_to (fun j => projection_partition_volume_sum P A j p)
    (projection_multiplicity_integral A p).
Proof.
move=> hE hP hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose beta := @euclidean_lebesgue_measure R m.
have hm := @euclidean_lebesgue_is_measure R m.
pose f := euclidean_projection_linear p.
apply: (@total_increasing_integral_values R Y beta hm
  (fun j y => (@partition_hit_count R X P (mapping_fibre f A y) j : extended_real_line R))
  (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R))
  (fun j => projection_partition_volume_sum P A j p) (projection_multiplicity_integral A p)).
- move=> j y; exact: (@measure_nonnegative R [the choiceType of (seq nat : Type)] _
    (counting_measure_is_measure R _) _).
- move=> y; exact: (@partition_hit_count_limit R X E P hE hP (mapping_fibre f A y)).
- move=> j; apply: (@suslin_partition_image_count_integral R X Y f beta hm E P hE hP A j _ hA).
  move=> S hS.
  apply: (@suslin_set_measurable R Y beta hm (f @` S)).
  + move=> C hC; exact (@borel_regular_borel_measurable R Y beta hm
      (@euclidean_lebesgue_borel_regular R m) C (closed_borel_set hC)).
  + exact: continuous_suslin_image (@euclidean_metric_complete R n)
      (euclidean_metric_separable R n) (@metric_hausdorff R Y)
      (@euclidean_projection_continuous R n m p) hS.
- exact: projection_multiplicity_suslin_integral_specification p hA.
Qed.
