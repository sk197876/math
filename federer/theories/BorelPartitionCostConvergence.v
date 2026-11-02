(** Federer (1969), 2.10.8, p. 175, second display: the costs of any
    sequence of Borel partitions converge to the constructed measure if
    their mesh tends to zero. No nesting or refinement is assumed. The proof
    only needs the partitions, so separability is unnecessary for this
    implication once the partitions are supplied. Extended-real order
    convergence includes infinite resulting measure. No relevant erratum
    correction occurs. *)
From mathcomp Require Import lra.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BorelPartition BorelCoverCostUP BorelCaratheodoryMeasure
  BorelPartitionCoverBounds MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  CaratheodoryScaleConvergence ExtendedRealBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_partition_cost_convergence_fine]: supporting
    form of the second display in Federer 2.10.8, p. 175.
    Uniform eventual smallness of all cell diameters suffices;
    this also covers empty partition families whose mesh supremum
    is negative infinity under the existing empty-supremum convention. *)
Theorem borel_partition_cost_convergence_fine (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (A : set X) (H : nat -> set (set X)) :
  (forall n, is_borel_partition A (H n)) ->
  (forall e : R, (0<e)%R -> exists N, forall n, (N<=n)%N ->
    forall B, H n B -> extended_metric_diameter B<=e%:E) ->
  extended_order_limit (fun n => borel_partition_cost c (H n)) (borel_caratheodory_measure c A).
Proof.
move=> hH hfine; split.
- move=> a ha.
  have hlim := @caratheodory_limit_positive_cutoff_convergence R X (@borel_metric_sets R X)
    (fun j => val j) (fun j => c (val j)) (borel_caratheodory_measure c) A
    (borel_caratheodory_specification c).
  have [d [hd hcut]] := hlim.1 a ha.
  pose e : R := (d/2)%R.
  have he : (0<e)%R by rewrite /e; apply: divr_gt0 hd _; rewrite ltr0n.
  have hed : (e<d)%R by rewrite /e; lra.
  have [N hN] := hfine e he; exists N=> n hn.
  have hdiam := hN n hn.
  have hb := @borel_partition_scale_bound R X c hc A (H n) e%:E
    (metric_scale_envelope (fun j : @borel_metric_sets R X => val j) (fun j => c (val j)) e%:E)
    (hH n) (metric_scale_envelope_specification _ _ e%:E) hdiam.
  apply: lt_le_trans _ hb; apply: hcut; by rewrite lte_fin.
- move=> b hb; exists 0%N=> n _.
  exact: le_lt_trans (@borel_partition_cost_upper R X c hc A (H n) (hH n)) hb.
Qed.

(** Source for [borel_partition_cost_convergence]: direct
    second displayed implication of Federer 2.10.8, p. 175.
    The supremum of diameters tends to zero in the existing
    extended-real order topology; the partition cost sums need
    not be monotone. No refinement, finiteness or global measure
    bound is added to the printed hypothesis. *)
Theorem borel_partition_cost_convergence (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (A : set X) (H : nat -> set (set X)) :
  (forall n, is_borel_partition A (H n)) ->
  extended_order_limit (fun n => extended_real_sup ((@extended_metric_diameter R X) @` H n)) 0 ->
  extended_order_limit (fun n => borel_partition_cost c (H n)) (borel_caratheodory_measure c A).
Proof.
move=> hH hmesh; apply: (@borel_partition_cost_convergence_fine R X c hc A H hH).
move=> e he.
have [N hN] := hmesh.2 e%:E ltac:(by rewrite lte_fin).
exists N=> n hn B hB.
apply: le_trans (_ : extended_metric_diameter B<=extended_real_sup
  ((@extended_metric_diameter R X) @` H n)) (ltW (hN n hn)).
apply: extended_real_sup_upper; by exists B.
Qed.
