(** Federer (1969), 2.10.9, p. 175, first sentence: apply the complete
    Borel-partition theorem to the actual integral-geometric gauge. The
    countable-cover hypothesis has been proved for this cost, not added as a
    premise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  BorelPartition BorelPartitionCoverBounds BorelPartitionCharacterization BorelPartitionCostConvergence
  MetricDiameter TopologicalBorel ExtendedRealBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_borel_partition_formula]: direct
    integral-geometric application of the first formula of 2.10.8
    in Federer 2.10.9, p. 175. All exponents at least one,
    all Borel targets and infinite resulting values are included. *)
Theorem integral_geometric_borel_partition_formula (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t -> borel_set A -> @integral_geometric_measure R n m hmn t A=
    extended_real_sup (borel_partition_cost_values (@integral_geometric_gauge R n m hmn t) A).
Proof.
move=> ht hA; have [D [hD hden]] := euclidean_metric_separable R n.
exact: (@borel_partition_cost_formula R (inner_metric_space (@euclidean_inner_productP R n))
  (@integral_geometric_gauge R n m hmn t) (@integral_geometric_gauge_borel_cover_cost R n m hmn t ht)
  D A hD hden hA).
Qed.

(** Source for [integral_geometric_shrinking_partition_limit]: direct
    integral-geometric application of the second formula of 2.10.8
    in Federer 2.10.9, p. 175. No nesting, refinement or finite
    measure assumption is added to the given Borel partitions. *)
Theorem integral_geometric_shrinking_partition_limit (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (H : nat -> set (set (inner_metric_space (@euclidean_inner_productP R n)))) :
  1<=t -> (forall k, is_borel_partition A (H k)) ->
  extended_order_limit (fun k => extended_real_sup
    ((@extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n))) @` H k)) 0 ->
  extended_order_limit (fun k => borel_partition_cost (@integral_geometric_gauge R n m hmn t) (H k))
    (@integral_geometric_measure R n m hmn t A).
Proof.
move=> ht; exact: (@borel_partition_cost_convergence R
  (inner_metric_space (@euclidean_inner_productP R n)) (@integral_geometric_gauge R n m hmn t)
  (@integral_geometric_gauge_borel_cover_cost R n m hmn t ht) A H).
Qed.
