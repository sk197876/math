(** Federer (1969), 3.1.4, p. 214: the scalar-target reduction
    uses finitely many target coordinates. A nonempty coordinate family
    also controls the missing domain of the original partial function. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanOneCoordinate EuclideanLebesgueDimensions LebesgueScalarMeasure
  CenteredBallRelations PartialFunctionUP PartialFunctionPostcomposition
  PartialFunctionPrecomposition MeasureApproximateLimitUP LocalZeroDensity
  EuclideanApproximateLimitCoordinates ScalarEuclideanApproximateLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_positive_approximate_limit_coordinates]:
    finite-coordinate reduction in Federer 3.1.4, p. 214, opening
    sentence of proof. Positive target dimension makes the explicit
    missing-domain clause follow from the first coordinate limit. *)
Lemma euclidean_positive_approximate_limit_coordinates (R : realType) m n
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R n.+1))) a y :
  is_measure_approximate_limit (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) f a y <->
  forall j : 'I_n.+1, @is_measure_approximate_limit R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (partial_function_postcompose f (fun v=>(v j : real_line_metric R))) a (y j).
Proof.
rewrite euclidean_approximate_limit_coordinate_criterion; split; first by move=> [].
move=> hc; split=> //.
have hd := approximate_limit_domain_density (hc ord0).
by rewrite partial_function_postcompose_domain in hd.
Qed.

(** Source for [scalar_source_euclidean_approximate_coordinates]:
    the finite-coordinate reduction in Federer 3.1.4, p. 214, applied
    to the scalar-parameter quotients defining ap D_i in 3.1.2. *)
Theorem scalar_source_euclidean_approximate_coordinates (R : realType) n
    (f : partial_function (real_line_metric R)
      (inner_metric_space (@euclidean_inner_productP R n.+1))) a y :
  @is_measure_approximate_limit R [the metricType R of real_line_metric R]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n.+1)]
    (@lebesgue_scalar_measure R)
    (@centered_closed_ball_relation R [the metricType R of real_line_metric R]) f a y <->
  forall j : 'I_n.+1, @is_measure_approximate_limit R
    [the metricType R of real_line_metric R] [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R)
    (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
    (partial_function_postcompose f (fun v=>(v j : real_line_metric R))) a (y j).
Proof.
rewrite scalar_euclidean_approximate_limit_iff euclidean_positive_approximate_limit_coordinates.
split=> hc j.
- apply: (scalar_euclidean_approximate_limit_iff _ _ _).2; exact: hc j.
- exact: (scalar_euclidean_approximate_limit_iff _ _ _).1 (hc j).
Qed.
