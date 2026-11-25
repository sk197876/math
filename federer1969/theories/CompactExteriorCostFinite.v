(** Finiteness of the compact-set cost supporting Federer (1969), 2.10.32,
    pp. 196–197. A compact set has finite real diameter. The project
    product-norm bound then gives a finite bound for its exterior supremum
    and hence its normalised cost. This supports choosing the actual volume
    and cost thresholds in the compact-class argument; it does not assume
    the desired volume inequality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CompactSetDistanceProfile CompactMetricBounded
  MetricDiameterUP MetricDiameter ExteriorDiameterBound ExteriorDiameterUP ExteriorDiameter
  ExteriorMeasureGauge HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_exterior_diameter_cost_finite]: supporting
    finite upper thresholds for compact convex
    members in 2.10.32, pp. 196–197.
    Convexity is unnecessary for this finiteness
    lemma; every natural degree is allowed. *)
Lemma compact_exterior_diameter_cost_finite (R : realType) (n m : nat)
    (K : compact_metric_set (inner_metric_space (@euclidean_inner_productP R n))) :
  (exterior_diameter_cost m (val K)< +oo)%E.
Proof.
pose d := compact_metric_diameter K.
have hd : 0<=d.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification (val K)).
  by rewrite compact_metric_diameter_finite_value lee_fin in hh.
have hdiam : (extended_metric_diameter (val K)<=d%:E)%E.
  by rewrite compact_metric_diameter_finite_value.
have hext := @extended_exterior_diameter_metric_bound R n m (val K) d hd hdiam.
have hc : (0<=(hausdorff_normalisation R m)%:E)%E.
  rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R m).
have hh := lee_wpmul2l hc hext.
rewrite -EFinM in hh.
exact: le_lt_trans hh (ltry _).
Qed.
