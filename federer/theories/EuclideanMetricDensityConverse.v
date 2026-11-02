(** Federer (1969), 3.2.17, pp. 254–255:
    source zero m-density is exactly the
    relative Lebesgue density used in the
    hypothesis. The reverse adapter uses the
    proved finite positive Euclidean ball volume. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanNoncenteredVitali
  PartialFunctionUP MeasureUP MeasureRestriction CenteredBallRelations MeasureSetDensity
  CenteredZeroDensityCriterion MetricClosedBalls MetricDensities MetricDensityZeroPowerMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_metric_zero_relative_zero_density]:
    the source density normalization in Federer
    3.2.17, p. 254. Exact ball volume
    converts every small r^m-mass bound to
    the relative Lebesgue density criterion. *)
Theorem euclidean_metric_zero_relative_zero_density (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R m))) a :
  partial_function_graph (metric_density m
    (measure_restrict (@euclidean_lebesgue_measure R m) A)) a 0%E ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) A) a 0%E.
Proof.
move=> hA.
have hm := euclidean_lebesgue_is_measure R m.
apply: (centered_small_mass_zero_density hm _ _).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
- move=> c hc.
  pose alpha := euclidean_unit_ball_volume R m.
  have ha : 0<alpha := (euclidean_unit_ball_volumeE R m).2.
  have he : 0<c*alpha/2 by rewrite divr_gt0 ?mulr_gt0 // ltr0n.
  have [d [hd hb]] := metric_zero_density_small_power_mass hm hA he.
  exists d; split=> // r hr hrd.
  have hRad : 0<r<=d by apply/andP; split=> //; exact: ltW hrd.
  apply: (le_lt_trans (hb r hRad) _).
  rewrite (euclidean_closed_ball_normalized_volume a (ltW hr)) -EFinM lte_fin.
  have hp : 0<r^+m by rewrite exprn_gt0.
  rewrite mulrA ltr_pM2r //.
  have hca : 0<c*alpha := mulr_gt0 hc ha.
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
Qed.
