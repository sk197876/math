(** Federer (1969), 3.2.17, p. 254:
    the upper density bound follows from the
    source enclosing-ball comparison at every positive
    radius. It requires no source-density premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBallVolume
  MeasureRestriction MetricDensities MetricDensityNumericalBounds
  PositiveRadiusLimitBounds MetricBiLipschitzUP EuclideanBiLipschitzMass HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_bilipschitz_upper_density]:
    Theta^*m(H^m restricted psi(K),psi(a))
    at most lambda^(2m), Federer 3.2.17,
    p. 254. All positive radii satisfy
    the same normalized bound. *)
Theorem euclidean_bilipschitz_upper_density (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R m)))
    (psi : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda : R) a :
  is_metric_bilipschitz_bound K psi lambda -> (0<lambda)%R -> K a ->
  upper_metric_density m (measure_restrict
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (psi @` K)) (psi a) <= (lambda^+(m+m))%R%:E.
Proof.
move=> hB hLam ha.
apply: (@positive_radius_upper_eventual_bound R _ _ 1%R (@ltr01 R))=> r /andP [hr _].
rewrite leNgt; apply/negP=> hbad.
have hlarge := metric_ball_density_value_large hr hbad.
have hbound := euclidean_bilipschitz_outer_ball_mass hB hLam ha hr.
by have := lt_le_trans hlarge hbound; rewrite ltxx.
Qed.
