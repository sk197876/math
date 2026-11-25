(** Federer (1969), 2.10.8, p. 175: both conclusions with the original
    countable-family hypothesis. The bridge to indexed covering costs is
    proved, rather than imposed as an extra hypothesis. A countable dense
    subset expresses exactly separability. Source context and supporting
    arguments: BorelCoverCostFamilies.v, BorelPartitionCharacterization.v
    and BorelPartitionCostConvergence.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum TopologicalBorel BorelPartition BorelCoverCostUP
  BorelCoverCostFamilies BorelCaratheodoryMeasure BorelPartitionCoverBounds
  BorelPartitionCharacterization BorelPartitionCostConvergence
  MetricDiameter ExtendedRealBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_8]: direct complete theorem
    of Federer 2.10.8, p. 175: the supremum over all Borel
    partition cost sums, and convergence for every sequence of
    Borel partitions whose supremum diameters tend to zero.
    Cost sums may be nonmonotone and the resulting measure may
    be infinite. No refinement relation is required. *)
Theorem federer_2_10_8 (R : realType) (X : metricType R)
    (c : set X -> \bar R) (D A : set X) :
  (forall B, borel_set B -> 0<=c B) ->
  (forall B G, countable G -> borel_set B -> (forall C, G C -> borel_set C) ->
    B `<=` \bigcup_(C in G) C -> c B<=nonnegative_sum G c) ->
  countable D -> dense D -> borel_set A ->
  borel_caratheodory_measure c A=extended_real_sup (borel_partition_cost_values c A) /\
  forall H : nat -> set (set X), (forall n, is_borel_partition A (H n)) ->
    extended_order_limit (fun n => extended_real_sup ((@extended_metric_diameter R X) @` H n)) 0 ->
    extended_order_limit (fun n => borel_partition_cost c (H n)) (borel_caratheodory_measure c A).
Proof.
move=> hnon hcover hD hden hA.
have hc := @borel_cover_cost_of_family_inequality R X c hnon hcover.
split.
- exact: (@borel_partition_cost_formula R X c hc D A hD hden hA).
- move=> H hH hmesh; exact: (@borel_partition_cost_convergence R X c hc A H hH hmesh).
Qed.
