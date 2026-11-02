(** Federer (1969), 2.10.9, p. 175, first sentence: the Borel-partition
    theorem applies to the Gross measure. Its actual projected-volume cost
    already satisfies the countable-cover inequality. Apply 2.10.8 with
    Euclidean separability proved, not assumed. The integral-geometric
    application and exponent limit are separate obligations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  ProjectedVolumeGauge ProjectionMeasure BorelPartition BorelCaratheodoryMeasure
  BorelPartitionCoverBounds BorelPartitionCharacterization BorelPartitionCostConvergence
  MetricDiameter TopologicalBorel ExtendedRealBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_measure_borel_partition_formula]: direct
    Gross-measure application in Federer 2.10.9, p. 175,
    of the supremum formula in 2.10.8. The target is any
    Borel subset of R^n and may have infinite measure. *)
Theorem gross_measure_borel_partition_formula (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (m<=n)%N -> borel_set A ->
  @gross_measure R n m A=extended_real_sup
    (borel_partition_cost_values (@projected_volume_gauge R n m) A).
Proof.
move=> hmn hA; have [D [hD hden]] := euclidean_metric_separable R n.
exact: (@borel_partition_cost_formula R (inner_metric_space (@euclidean_inner_productP R n))
  (@projected_volume_gauge R n m) (@projected_volume_gauge_borel_cover_cost R n m hmn)
  D A hD hden hA).
Qed.

(** Source for [gross_measure_shrinking_partition_limit]: direct
    Gross-measure application of the second conclusion of
    Federer 2.10.8, cited in 2.10.9, p. 175. No nesting,
    refinement or finite-value requirement is added. *)
Theorem gross_measure_shrinking_partition_limit (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (H : nat -> set (set (inner_metric_space (@euclidean_inner_productP R n)))) :
  (m<=n)%N -> (forall k, is_borel_partition A (H k)) ->
  extended_order_limit (fun k => extended_real_sup
    ((@extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n))) @` H k)) 0 ->
  extended_order_limit (fun k => borel_partition_cost (@projected_volume_gauge R n m) (H k))
    (@gross_measure R n m A).
Proof.
move=> hmn; exact: (@borel_partition_cost_convergence R
  (inner_metric_space (@euclidean_inner_productP R n)) (@projected_volume_gauge R n m)
  (@projected_volume_gauge_borel_cover_cost R n m hmn) A H).
Qed.
