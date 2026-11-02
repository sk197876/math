(** Federer (1969), 3.2.16, p. 254:
    comparison with 3.1.2 uses normalized Euclidean
    ball volume. This adapter translates relative
    Lebesgue density zero to metric m-density zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume
  PartialFunctionUP MeasureRestriction CenteredBallRelations MeasureSetDensity MeasureUP
  EuclideanZeroDensitySmallMass MetricClosedBalls MetricDensities
  MetricDensityZeroPowerMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_relative_zero_metric_zero_density]:
    the density translation underlying the corrected
    word "generalizes", Federer 3.2.16, p. 254
    line 2; erratum p. 5. The denominator
    is alpha(m)r^m, the exact Lebesgue ball volume. *)
Theorem euclidean_relative_zero_metric_zero_density (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) a :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) A) a 0%E ->
  partial_function_graph (metric_density n
    (measure_restrict (@euclidean_lebesgue_measure R n) A)) a 0%E.
Proof.
move=> hA.
have hm := euclidean_lebesgue_is_measure R n.
apply: (small_power_mass_metric_zero_density hm _)=> e he.
pose alpha := euclidean_unit_ball_volume R n.
have ha : 0<alpha := (euclidean_unit_ball_volumeE R n).2.
have hc : 0<e/alpha by rewrite divr_gt0.
have [d [hd hb]] := euclidean_zero_density_small_mass hA hc.
exists d; split=> // r /andP [hr hrd].
have hh := hb r hr hrd.
rewrite (euclidean_closed_ball_normalized_volume a (ltW hr)) -EFinM in hh.
have hEq : e/alpha*(alpha*r^+n)=e*r^+n.
  by rewrite mulrA divfK ?gt_eqF //.
rewrite hEq in hh; exact: ltW hh.
Qed.
