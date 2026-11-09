(** Federer (1969), 3.3.21, p. 309: the actual original diverging-schedule Cantor-square example. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  CantorSquareCompactMass PowerCantorPairUP PowerCantorPair ScheduledPowerCantorSetUP ScheduledPowerCantorSetSealed
  PowerCantorSquarePositiveFinite ScheduledCantorLowerDensityZero DivergingCantorScheduleUP
  RealMetricDensities RealHausdorffMeasure MeasureRestriction MeasureAlmostUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_3_21]: the entire mathematical example
    of 3.3.21, p. 309. The actual original opaque factor has
    arbitrary original n_j>= 2 tending to infinity and every real
    0<m<1. Its square is compact with actual positive finite
    H^(2m), and its actual lower 2m-density is zero at EVERY
    centre, strengthening the printed almost-everywhere assertion.
    Only the exposed original factor laws are used. *)
Theorem federer_3_3_21 (R:realType) (m:R) (hm:0<m) (hm1:m<1)
    (hp:0<= 2 * m) n (hn:forall j,(2<=n j)%N):
  cantor_schedule_tends_infinity n ->
  let A:=@ScheduledPowerCantor.value R m hm hm1 n hn in
  let E:=euclidean_cantor_product A A in
  let X:=inner_metric_space (@euclidean_inner_productP R 2) in
  let mu:=@real_hausdorff_measure R X (2 * m) hp in
  compact E /\(0<mu E< +oo)%E /\
  (forall a:X,lower_real_metric_density hp (measure_restrict mu E) a= 0%E) /\
  measure_almost_everywhere_on mu E [set a:X|lower_real_metric_density hp (measure_restrict mu E) a= 0%E].
Proof.
move=>hDiverge A E X mu.
have [f hPair]:=@ScheduledPowerCantor.laws R m hm hm1 n hn.
have hFactor:=(@power_cantor_pair_properties R 1 m n A f ltr01 hm hm1 hPair).1.
have hDensity:=@scheduled_original_cantor_square_lower_density_zero R 1 m hp n A f
  ltr01 hm hm1 hn hDiverge hPair.
split;first exact:(euclidean_cantor_product_compact hFactor hFactor).
split;first exact:(@power_cantor_original_square_positive_finite R 1 m hp n A f ltr01 hm hm1 hPair).
split;first exact:hDensity.
have hEmpty:E `\` [set a:X|lower_real_metric_density hp (measure_restrict mu E) a= 0%E]=set0.
  apply/seteqP;split;last by move=>a [].
  move=>a [ha hNo];exfalso;exact:hNo (hDensity a).
rewrite /measure_almost_everywhere_on hEmpty.
exact:measure_empty (real_hausdorff_measure_is_measure X hp).
Qed.
