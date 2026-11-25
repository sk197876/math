(** Federer (1969), 3.1.7, p. 217: restriction of an
    ordinary partial derivative to a coordinate section of density one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates RealNormUP
  NormMetric RealMetricBackground NormPartialDerivative NormedCurveDerivativeUP
  PartialFunctionUP ApproximatePartialDerivativeUP ApproximateDifferentialLocal
  LebesgueScalarMeasure ScalarEuclideanApproximateLimits CenteredNullSetDensity
  CenteredZeroDensityUnion LocalZeroDensity EuclideanApproximateContext
  CenteredBallRelations MetricClosedBalls MeasureSetDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [ordinary_partial_on_density_domain]: the last
    inference in Federer 3.1.7, p. 217. The complement
    of the actual coordinate section has scalar density zero;
    the ordinary quotient limit of the extension then remains
    the approximate quotient limit on the restricted domain. *)
Theorem ordinary_partial_on_density_domain (R : realType) m (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (A : set (R_n R m))
    (f g : R_n R m->Y) (a : R_n R m) (i : 'I_m) (v : Y) :
  (forall x, A x -> f x=g x) -> A a ->
  partial_function_graph
    (@measure_set_density R [the metricType R of real_line_metric R]
      (@lebesgue_scalar_measure R)
      (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
      [set t : real_line_metric R | ~A (a+t*:(@coordinate_basis R m i))]) 0 0%E ->
  has_norm_partial_derivative NY g a i v ->
  has_approximate_partial_derivative hNY A f a i v.
Proof.
move=> hfg ha hA hv; split=> // W hW.
have hz := @centered_null_set_density_zero R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) [set 0] 0 (lebesgue_scalar_is_measure R)
  (@scalar_centered_ball_positive_finite R) (lebesgue_scalar_singleton 0).
have hbad := @centered_zero_density_union R
  [the metricType R of real_line_metric R] (@lebesgue_scalar_measure R) _ _ 0
  (lebesgue_scalar_is_measure R) (@scalar_centered_ball_positive_finite R) hA hz.
have [e he heW] := (metricType_numDomainType.nbhs_mdistP
  (v : real_norm_metric_space hNY) W).1 hW.
have [d [hd hdq]] := hv e he.
apply: (@local_zero_density_mono R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R)
  (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
  _ ([set t : real_line_metric R | ~A (a+t*:(@coordinate_basis R m i))] `|` [set 0])
  [set t | mdist (0 : real_line_metric R) t<d] 0
  (scalar_approximate_context R) (metric_open_ball_open _ _) _ _ hbad).
- change (is_true (mdist (0 : real_line_metric R) 0<d)).
  by rewrite mdistxx.
- move=> t ht hn; apply: contrapT=> hnone.
  have ht0 : t!=0 by apply/eqP=> h; apply: hnone; right; exact h.
  have hAt : A (a+t*:(@coordinate_basis R m i)).
    apply: contrapT=> h; apply: hnone; left; exact h.
  have hnorm : 0<`|t|<d.
    rewrite normr_gt0 ht0 /=.
    change (is_true (mdist (0 : real_line_metric R) t<d)) in ht.
    by move: ht; rewrite real_line_metric_distanceE sub0r normrN.
  apply: hn.
  exists (t^-1*:(f (a+t*:(@coordinate_basis R m i))-f a)); split.
  + apply: (@approximate_partial_quotient_graph R m Y NY hNY A f a i t _).2.
    by split=> //; split.
  + apply: heW.
    change (is_true (NY (v-t^-1*:(f (a+t*:(@coordinate_basis R m i))-f a))<e)).
    rewrite (real_seminorm_subtract hNY.1) (hfg _ hAt) (hfg a ha).
    exact: hdq t hnorm.
Qed.
