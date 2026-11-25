(** Federer (1969), 3.3.20, p. 308:
    exact original factor-piece masses for the square hit argument. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  EqualCostIntervalTreeUP EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP
  SpecialIntervalTreeMass PowerCantorCoefficientInvariance PowerConcaveIntervalGauge
  MetricRealPowerMeasure MetricRealPowerIntervalAgreement RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_original_unit_piece_mass]:
    each ORIGINAL interval piece has actual unit-gauge
    mass equal to its width to power m. This
    supplies the actual square-piece weights in 3.3.20,
    p. 308. Coefficient invariance preserves the original
    tree and limit, and actual 2.10.28(3) proves
    exact mass without a new measurability premise. *)
Theorem power_cantor_original_unit_piece_mass (R:realType) (c m:R)
    (J:compact_real_intervals R) n H (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  is_special_interval_tree_limit H A ->forall j S,S \in H j ->
  @metric_real_power_measure R [the metricType R of real_line_metric R] 1 m (A `&` val S)=
    (real_power (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))) m)%:E.
Proof.
move=>hc hm hm1 hTree hA j S hS.
have hUnit:=@power_cantor_tree_coefficient_change R c 1 m J n H hc ltr01 hTree.
have hGauge:=@power_concave_interval_gauge R 1 m ltr01 hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hGauge J n H hUnit.
have hMass:=(@federer_2_10_28_3 R _ hGauge H hSpecial A hA).2 j S hS.
rewrite /concave_interval_cost mul1r in hMass.
rewrite (@metric_real_power_interval_measure_agreement R 1 m ler01 (ltW hm)).
exact:hMass.
Qed.
