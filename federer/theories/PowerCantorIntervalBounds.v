(** Federer (1969), 2.10.29, p. 194: the two interval bounds used in each
    product case. One factor has its ordinary c*d^m bound from 2.10.28(3),
    while the factor whose test length lies between subdivision spacing and
    parent width has the factor-six linear bound. Use the actual
    unrestricted real power-gauge measure through the proved interval
    agreement. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower MetricDiameter MetricDiameterReal CompactIntervalGauge
  PowerCantorPairUP PowerConcaveIntervalGauge EqualCostCantorMass EqualCostTreeLinearBound
  InterleavedCantorScalesUP MetricRealPowerMeasure MetricRealPowerIntervalAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_pair_interval_bound]: direct
    c*d^m bound from 2.10.28(3), p. 192,
    used for either factor in 2.10.29,
    p. 194. The coefficient remains explicit
    and the diameter is the actual finite
    diameter of the compact test interval. *)
Theorem power_cantor_pair_interval_bound (R : realType) (c m : R) n A f :
  0<c -> 0<m -> m<1 -> is_power_cantor_pair c m n A f ->
  forall T : compact_real_intervals R,
    (@metric_real_power_measure R [the metricType R of real_line_metric R] c m (A `&` val T)<=
      (c*real_power (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))) m)%:E)%E.
Proof.
move=> hc hm hm1 [J [H [hJ [ht [hA hf]]]]] T.
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have [_ [_ [_ hb]]] := @equal_cost_interval_limit_mass R _ hg J n H A ht hA.
rewrite (@metric_real_power_interval_measure_agreement R c m (ltW hc) (ltW hm)).
exact (hb T).
Qed.

(** Source for [interleaved_power_cantor_left_linear_bound]: direct
    first-factor 6*c*s_j^m*d/s_j bound in
    the second case of 2.10.29, p. 194.
    The test length is between t_(j+1)
    and s_j in zero-based spacing notation. *)
Theorem interleaved_power_cantor_left_linear_bound (R : realType) (c m : R) D A f :
  0<c -> 0<m -> m<1 -> is_interleaved_cantor_scales (fun t=>c*real_power t m) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  forall j (T : compact_real_intervals R),
    cantor_left_spacing D j<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)) ->
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))<=cantor_left_width D j ->
    (@metric_real_power_measure R [the metricType R of real_line_metric R] c m (A `&` val T)<=
      (6*(c*real_power (cantor_left_width D j) m)*
        fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/
        cantor_left_width D j)%:E)%E.
Proof.
move=> hc hm hm1 hD [J [H [hJ [ht [hA hf]]]]] j T hlarge hsmall.
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have hroot : cantor_left_width D 0%N=
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
  by rewrite (interleaved_cantor_left_root hD) hJ (extended_metric_diameter_segment ler01) subr0.
rewrite (@metric_real_power_interval_measure_agreement R c m (ltW hc) (ltW hm)).
exact (@equal_cost_tree_uniform_linear_mass_bound R _ hg J (cantor_left_subdivision D) H ht A hA
  (cantor_left_width D) (cantor_left_spacing D) hroot
  (interleaved_cantor_left_split hD) (interleaved_cantor_left_spacing_law hD) j T hlarge hsmall).
Qed.

(** Source for [interleaved_power_cantor_right_linear_bound]: direct
    second-factor 6*c*sigma_(j-1)^m*d/sigma_(j-1)
    bound in the first case of 2.10.29,
    p. 194. The compact test length lies
    between tau_j and sigma_(j-1); spacing
    indices are shifted down by one here. *)
Theorem interleaved_power_cantor_right_linear_bound (R : realType) (c m : R) D A f :
  0<c -> 0<m -> m<1 -> is_interleaved_cantor_scales (fun t=>c*real_power t m) D ->
  is_power_cantor_pair c m (cantor_right_subdivision D) A f ->
  forall j (T : compact_real_intervals R),
    cantor_right_spacing D j<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)) ->
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))<=cantor_right_width D j ->
    (@metric_real_power_measure R [the metricType R of real_line_metric R] c m (A `&` val T)<=
      (6*(c*real_power (cantor_right_width D j) m)*
        fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/
        cantor_right_width D j)%:E)%E.
Proof.
move=> hc hm hm1 hD [J [H [hJ [ht [hA hf]]]]] j T hlarge hsmall.
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have hroot : cantor_right_width D 0%N=
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
  by rewrite (interleaved_cantor_right_root hD) hJ (extended_metric_diameter_segment ler01) subr0.
rewrite (@metric_real_power_interval_measure_agreement R c m (ltW hc) (ltW hm)).
exact (@equal_cost_tree_uniform_linear_mass_bound R _ hg J (cantor_right_subdivision D) H ht A hA
  (cantor_right_width D) (cantor_right_spacing D) hroot
  (interleaved_cantor_right_split hD) (interleaved_cantor_right_spacing_law hD) j T hlarge hsmall).
Qed.
