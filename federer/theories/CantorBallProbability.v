(** Federer (1969), 3.4.4, p. 318: the
    actual original Cantor factor probability and its real-degree growth. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricClosedBalls
  MetricDiameter MetricDiameterReal RealPower PowerCantorPairUP PowerCantorPair
  PowerCantorProductMeasure PowerCantorIntervalBounds MetricRealPowerMeasure
  MetricRealPowerClosedCovers MetricRealPowerIntervalAgreement BallGrowthProbabilityUP
  MeasureUP MeasureRestriction BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [original_cantor_ball_probability_exists]: the
    original A(beta,n) factor in the product image of
    3.4.4, p. 318. Its actual unit power
    measure restricted to the original Cantor set has mass
    one by 2.10.28. A radius-r ball is the compact
    interval of length 2r, including r=0; the original
    interval bound proves the real-degree growth law. *)
Theorem original_cantor_ball_probability_exists (R:realType) (beta:R) n
    (A:set (real_line_metric R)) (f:R->R):
  (0<beta)%R ->(beta<1)%R ->is_power_cantor_pair 1 beta n A f ->
  exists mu:set (real_line_metric R)->\bar R,
    is_ball_growth_probability A (real_power 2 beta) beta mu.
Proof.
move=>hBeta hBetaUpper hPair.
pose L:=[the metricType R of real_line_metric R].
pose mu:=power_cantor_restricted_measure 1 beta A.
have hMeasure:is_measure mu:=@power_cantor_restricted_is_measure R 1 beta A ler01.
have hMass:@metric_real_power_measure R L 1 beta A= 1.
  exact:(power_cantor_pair_real_power_mass ltr01 hBeta hBetaUpper hPair).1.
have hClosedA:closed A.
  exact:compact_closed (@metric_hausdorff R L) (power_cantor_pair_properties ltr01 hBeta hBetaUpper hPair).1.
exists mu;constructor.
- exact:hMeasure.
- by rewrite /mu /power_cantor_restricted_measure /measure_restrict setIT hMass.
- move=>C hC;apply:measure_restrict_measurable.
  apply:(borel_regular_borel_measurable
    (@metric_real_power_measure_is_measure R L 1 beta ler01)
    (@metric_real_power_measure_borel_regular R L 1 beta ler01)).
  exact:closed_borel_set hC.
- exact:hClosedA.
- by rewrite /mu /power_cantor_restricted_measure /measure_restrict setIid hMass.
- have hTwo:(0<(2:R))%R by rewrite ltr0n.
  exact:real_power_strictly_positive _ hTwo.
- exact:ltW hBeta.
- move=>a r hr.
  have hOrder:(a-r<=a+r)%R by lra.
  have hInterval:is_compact_real_interval (`[(a-r)%R,(a+r)%R]:set (real_line_metric R)).
    exists (a-r)%R,(a+r)%R;by split.
  pose T:compact_real_intervals R:=Sub (`[(a-r)%R,(a+r)%R]:set (real_line_metric R)) (mem_set hInterval).
  have hBall:metric_closed_ball a r=val T.
    apply/seteqP;split=>x hx.
    + have h:(`|a-x|<=r)%R:=hx.
      move:h;rewrite ler_norml=>/andP[hLow hHigh].
      rewrite /T /= /mkset in_itv /=;apply/andP;split;lra.
    + have /andP[hLow hHigh]:(a-r<=x<=a+r)%R by move:hx;rewrite /T /= /mkset in_itv /=.
      change (is_true (`|a-x|<=r)%R);rewrite ler_norml;apply/andP;split;lra.
  have hLength:(fine (@extended_metric_diameter R L (val T))= 2*r)%R.
    rewrite /T /= (extended_metric_diameter_segment hOrder) /=;by ring.
  have hBound:=@power_cantor_pair_interval_bound R 1 beta n A f ltr01 hBeta hBetaUpper hPair T.
  rewrite hLength mul1r in hBound.
  have hTwo:(0<=(2:R))%R by rewrite ler0n.
  rewrite /mu /power_cantor_restricted_measure /measure_restrict hBall.
  by rewrite (@real_power_product R 2 r beta hTwo hr) in hBound.
Qed.
