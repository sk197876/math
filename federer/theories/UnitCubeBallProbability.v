(** Federer (1969), 3.4.4, p. 318: the
    Euclidean factor probability for positive real-degree product mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanClosedBallVolume EuclideanBallVolume
  MeasureUP MeasureBasic MeasureRestriction BorelRegularMeasureUP TopologicalBorel
  MetricClosedBalls BallGrowthProbabilityUP RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_cube_ball_probability_exists]: the original
    R^nu factor in the positive product image of 3.4.4,
    p. 318. Restrict its actual Lebesgue measure to
    the unit cube, whose mass is one. Actual closed-ball
    volume proves the growth bound. Dimension and radius zero
    retain their printed empty-product conventions. *)
Theorem unit_cube_ball_probability_exists (R:realType) nu:
  exists mu:set (inner_metric_space (@euclidean_inner_productP R nu))->\bar R,
    is_ball_growth_probability setT (euclidean_unit_ball_volume R nu) nu%:R mu.
Proof.
pose E:=[the metricType R of inner_metric_space (@euclidean_inner_productP R nu)].
pose Leb:=@euclidean_lebesgue_measure R nu.
pose C:set E:=fun x=>forall i,(0<x i<1)%R.
pose mu:=measure_restrict Leb C.
have hLeb:is_measure Leb:=euclidean_lebesgue_is_measure R nu.
have hMu:is_measure mu:=measure_restrict_is_measure hLeb C.
have hMass:mu setT= 1.
  rewrite /mu /measure_restrict setIT.
  exact:euclidean_unit_cube.
exists mu;constructor.
- exact:hMu.
- exact:hMass.
- move=>D hD;apply:measure_restrict_measurable.
  apply:(borel_regular_borel_measurable hLeb (euclidean_lebesgue_borel_regular R nu)).
  exact:closed_borel_set hD.
- exact:closedT.
- exact:hMass.
- exact:(euclidean_unit_ball_volumeE R nu).2.
- by rewrite ler0n.
- move=>x r hr.
  have hSubset:C `&` metric_closed_ball x r `<=` metric_closed_ball x r by move=>y [_ hy].
  have hBound:=le_trans (measure_mono hLeb hSubset) (euclidean_closed_ball_volume_upper x hr).
  by rewrite (@real_power_natural_exponent R r nu hr).
Qed.
