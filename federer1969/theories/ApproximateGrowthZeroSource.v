(** Federer (1969), 3.1.8, pp. 217–218: the zero-dimensional-source boundary
    of the approximate growth hypothesis. This supporting interpretation
    follows the actual punctured quotient of 3.1.2, p. 212, and the
    unit-mass empty-product Lebesgue convention; it is not a separate
    assertion printed in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanApproximateContext CenteredBallRelations PartialFunctionUP
  MeasureSetDensity MeasureApproximateOrderLimits ApproximateOrderThresholdRays
  ApproximateLimitEmptyDomain ApproximateMetricGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [zero_source_finite_approximate_growth_domain_empty]:
    supporting zero-dimensional interpretation of Federer 3.1.8,
    pp. 217–218. The punctured growth quotient on the singleton source
    has empty domain. A finite approximate upper limit would force
    the whole source to have density zero, so the hypothesis can hold
    at every domain point only when the domain is empty. *)
Theorem zero_source_finite_approximate_growth_domain_empty (R : realType)
    (Y : metricType R)
    (A : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (f : inner_metric_space (@euclidean_inner_productP R 0)->Y) :
  (forall a, A a -> (measure_approximate_upper_limit
    (@euclidean_lebesgue_measure R 0)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)])
    (partial_metric_growth_quotient A f a) a < +oo)%E) ->
  A=set0.
Proof.
move=> hg; apply/seteqP; split=> a; last by case.
move=> ha.
pose X := inner_metric_space (@euclidean_inner_productP R 0).
pose mu := @euclidean_lebesgue_measure R 0.
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose F := partial_metric_growth_quotient A f a.
have [q [_ hq]] := (approximate_upper_limit_rational_ray
  (euclidean_approximate_context R 0) F a +oo%E).1 (hg a ha).
have he : partial_function_preimage F [set y | (y<=(ratr q : R)%:E)%E]=set0.
  apply/seteqP; split=> x; last by case.
  move=> [y [[[hx hne] hy] hqy]].
  by move: hne; rewrite (coordinate_zero x) (coordinate_zero a) eqxx.
change (partial_function_graph
  (measure_set_density mu V (~` partial_function_preimage F
    [set y | (y<=(ratr q : R)%:E)%E])) a 0%E) in hq.
rewrite he setC0 in hq.
exact: (whole_set_density_not_zero (euclidean_approximate_context R 0) hq).
Qed.
