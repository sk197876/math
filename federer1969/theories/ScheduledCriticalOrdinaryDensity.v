(** Federer (1969), 3.3.21, p. 309: the original critical example has ordinary lower one-density zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  PowerCantorPairUP PowerCantorSquarePositiveFinite ScheduledCantorLowerDensityZero DivergingCantorScheduleUP
  RealMetricDensities RealHausdorffMeasure HausdorffMeasure MetricDensities MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_critical_square_ordinary_density_zero]: at
    original m= 1/2, the actual positive finite H1 measure of E
    has ordinary lower one-density zero at EVERY centre. This is
    the natural-degree specialization of 3.3.21, p. 309; actual
    real-degree Hausdorff and density compatibility discharge the
    change of notation without an added normalization premise. *)
Theorem scheduled_critical_square_ordinary_density_zero (R:realType) (c:R)
    n (A:set (real_line_metric R)) (f:R->R):
  0<c ->(forall j,(2<=n j)%N) ->cantor_schedule_tends_infinity n ->
  is_power_cantor_pair c (1/2:R) n A f ->
  let X:=inner_metric_space (@euclidean_inner_productP R 2) in
  let E:=euclidean_cantor_product A A in
  let H1:=@hausdorff_measure R X 1 in
  (0<H1 E< +oo)%E /\forall a:X,lower_metric_density 1 (measure_restrict H1 E) a= 0%E.
Proof.
move=>hc hn hDiverge hPair X E H1.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have hp:0<= 2 * (1/2:R) by lra.
have hFinite:=@power_cantor_original_square_positive_finite R c (1/2:R) hp n A f hc hm hm1 hPair.
have hZero:=@scheduled_original_cantor_square_lower_density_zero R c (1/2:R) hp n A f
  hc hm hm1 hn hDiverge hPair.
have hScalar:2 * (1/2:R)= 1 by field.
move:hp hFinite hZero;rewrite hScalar=>hp hFinite hZero.
have hMeasure:(@real_hausdorff_measure R X 1 hp)=H1.
  apply:funext=>B;exact:(@real_hausdorff_measure_natural R X 1 hp B).
rewrite hMeasure in hFinite hZero.
split;first exact:hFinite.
move=>a;have h:=hZero a.
by rewrite (@lower_real_metric_density_natural R X 1 hp (measure_restrict H1 E) a) in h.
Qed.
