(** Federer (1969), 3.3.4, p. 291:
    zero or infinite actual reference upper
    ratios imply the original unnormalized open-ball
    alternatives. The zero alternative is an
    ordinary limit over all positive radii. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext
  MetricClosedBalls MetricDensities EuclideanBallVolume NullBallLocus
  PositiveRadiusLimits PositiveRightOrderLimit RadialBallRatios
  StructureLiteralBallRatio StructureOpenBallGrowth StructurePositiveGrowthLimits
  StructureZeroLimitComparison StructureInfiniteLimitComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_ratio_open_ball_limit]:
    the zero alternative after applying 2.9.17
    in Federer 3.3.4, p. 291. Density one
    and positive finite reference denominators transfer
    the actual zero upper ratio to an ordinary
    zero limit of the original open-ball costs. *)
Theorem structure_zero_ratio_open_ball_limit (R:realType) (X:metricType R)
    m (phi psi:set X->\bar R) (x:X):
  is_derivation_measure phi ->is_measure psi ->
  ~measure_null_ball_points phi x ->
  positive_right_extended_order_limit (metric_ball_density m phi x) 1%E ->
  centered_ball_ratio_upper_limit psi phi x=0%E ->
  positive_right_extended_order_limit (structure_open_ball_growth m psi x) 0%E.
Proof.
move=>hPhi hPsi hNo hDensity hZero.
have [d [hd hCompare]]:=structure_open_ball_ratio_comparisons hPhi hPsi hNo hDensity.
have hOrdinary:positive_right_extended_order_limit
    (fun r:R=> (psi (metric_closed_ball x r)/phi (metric_closed_ball x r))%E) 0%E.
  apply:structure_nonnegative_zero_upper_limit_ordinary.
  - move=>r hr; apply:mule_ge0; first exact:measure_nonnegative hPsi _.
    rewrite inve_ge0; exact:measure_nonnegative (derivation_measure_law hPhi) _.
  - by rewrite -(structure_literal_positive_ball_ratio psi hPhi hNo).
have hK:0<2*euclidean_unit_ball_volume R m.
  by rewrite mulr_gt0 ?ltr0n //; exact:(euclidean_unit_ball_volumeE R m).2.
apply:(@structure_zero_limit_scaled_comparison R _ _ 1
  (2*euclidean_unit_ball_volume R m) d ltr01 hK hd).
- move=>r hr; exact:structure_open_ball_growth_nonnegative hPsi hr.
- move=>r hr; rewrite mul1r; exact:(hCompare r hr).1.
- exact:hOrdinary.
Qed.

(** Source for [structure_infinite_ratio_open_ball_upper_limit]:
    the infinite alternative after applying 2.9.17
    in Federer 3.3.4, p. 291. Original
    closed r-balls lie in open 2r-balls;
    density one gives a finite positive scalar
    comparison, preserving an infinite upper limit. *)
Theorem structure_infinite_ratio_open_ball_upper_limit (R:realType) (X:metricType R)
    m (phi psi:set X->\bar R) (x:X):
  is_derivation_measure phi ->is_measure psi ->
  ~measure_null_ball_points phi x ->
  positive_right_extended_order_limit (metric_ball_density m phi x) 1%E ->
  centered_ball_ratio_upper_limit psi phi x=+oo%E ->
  positive_radius_upper_limit (structure_open_ball_growth m psi x)=+oo%E.
Proof.
move=>hPhi hPsi hNo hDensity hInfinite.
have [d [hd hCompare]]:=structure_open_ball_ratio_comparisons hPhi hPsi hNo hDensity.
have hK:0<(2:R)^+m/(euclidean_unit_ball_volume R m/2).
  rewrite divr_gt0 ?exprn_gt0 ?ltr0n // divr_gt0 ?ltr0n //.
  exact:(euclidean_unit_ball_volumeE R m).2.
apply:(@structure_infinite_limit_scaled_comparison R
  (fun r:R=> (psi (metric_closed_ball x r)/phi (metric_closed_ball x r))%E)
  (structure_open_ball_growth m psi x) 2
  ((2:R)^+m/(euclidean_unit_ball_volume R m/2)) d _ hK hd).
- by rewrite ltr0n.
- move=>r hr; exact:(hCompare r hr).2.
- by rewrite -(structure_literal_positive_ball_ratio psi hPhi hNo).
Qed.
