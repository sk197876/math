(** Federer (1969), 3.3.21, p. 309: original real-degree lower density vanishes for every diverging schedule. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From mathcomp Require Import ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP PowerCantorPairUP PowerCantorWidthExistence
  PowerCantorUniformGapScalar ScheduledCantorSparseDensity DivergingCantorScheduleUP DivergingScheduleSparseScales
  RealMetricDensities RealHausdorffMeasure RealHausdorffNormalisation RealPower
  EuclideanInnerProduct InnerMetric EuclideanCantorProduct MeasureUP MeasureRestriction
  PositiveRadiusUnboundedValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_original_cantor_square_lower_density_zero]:
    the actual lower 2m-density of the original restricted Hausdorff
    measure is zero for EVERY centre, strengthening the almost-everywhere
    assertion of 3.3.21, p. 309. At every prescribed small-radius
    cutoff and error an actual original level supplies a genuine
    sparse radius with proved density bound. The full positive-radius
    lower-limit laws, rather than a sampled upper limit, finish the proof.
    Every original real 0<m<1 and every schedule tending to infinity
    remain; no rate, monotonicity, density or gap premise is supplied. *)
Theorem scheduled_original_cantor_square_lower_density_zero (R:realType) (c m:R)
    (hp:0<= 2 * m) n (A:set (real_line_metric R)) (f:R->R):
  0<c ->0<m ->m<1 ->(forall j,(2<=n j)%N) ->cantor_schedule_tends_infinity n ->
  is_power_cantor_pair c m n A f ->
  forall a:inner_metric_space (@euclidean_inner_productP R 2),
  lower_real_metric_density hp
    (measure_restrict (@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2))
      (2 * m) hp) (euclidean_cantor_product A A)) a= 0%E.
Proof.
move=>hc hm hm1 hn hDiverge [J [H [hJ [hTree [hA _]]]]] a.
have [w hW]:=power_cantor_original_widths_exist hc hm hm1 hn.
pose k:= 1-2 * real_power (2:R) (-m^-1).
pose K:=real_power 2 m * real_power (3/(2 * k)) (2 * m).
have hk:0<k:=(andP (power_cantor_uniform_gap_positive hm hm1)).1.
have hK:0<K.
  apply:mulr_gt0;apply:real_power_strictly_positive;first by rewrite ltr0n.
  by rewrite divr_gt0 // mulr_gt0 // ltr0n.
have hP:0<2-2 * m by lra.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose mu:=measure_restrict (@real_hausdorff_measure R X (2 * m) hp) (euclidean_cantor_product A A).
have hMu:is_measure mu:=measure_restrict_is_measure (real_hausdorff_measure_is_measure X hp) _.
apply:(@positive_radius_lower_zero_from_small_values R (real_metric_ball_density hp mu a)).
- move=>r hr;exact:real_metric_ball_density_nonnegative hMu hr.
- move=>e d he hd.
  have [N hN]:=@diverging_schedule_original_sparse_scalars R n k K (2-2 * m) e d
    hDiverge hk hK hP he hd.
  have [_ [hRadius hSmall]]:=hN N (leqnn N).
  have [[hr hBound] hDensity]:=@scheduled_original_sparse_ball_density_bound R c m hp J n H w A N a
    hc hm hm1 hn hJ hTree hA hW.
  pose r:=k * w N/(3 * (n N)%:R).
  exists r;split;first by apply/andP;split;[exact:hr|exact:le_lt_trans hBound hRadius].
  apply:le_trans hDensity _;rewrite lee_fin.
  have hExponent:2 * m-2= -(2-2 * m) by ring.
  rewrite hExponent;exact:ltW hSmall.
Qed.
