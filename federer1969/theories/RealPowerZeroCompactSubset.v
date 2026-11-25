(** Federer (1969), 2.10.47, p. 204: at degree zero a singleton gives finite
    positive measure. This proves the statement for every explicit positive
    constant gauge coefficient, so the real-degree theorem includes zero
    without a normalisation assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter RealPowerSingletonBound RealPower MetricRealPowerCost MetricRealPowerMeasureUP
  MetricRealPowerMeasureLaws HausdorffLengthUP CaratheodoryLimitUP MetricScaleEnvelope
  MetricScaleMeasureBound PointMassMeasure FiniteMeasureScaling MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_zero_singleton]: exact singleton
    value of the constant degree-zero gauge in 2.10.2(1),
    p. 171, used in 2.10.47, p. 204. *)
Theorem real_power_zero_singleton (R : realType) (X : metricType R) c mu (x : X) :
  is_metric_real_power_measure c 0%R mu -> (0<=c)%R -> mu [set x]=c%:E.
Proof.
move=> hmu hc.
have hu := @real_power_singleton_bound R X c 0%R mu x hmu hc.
rewrite real_power_zero_exponent mulr1 in hu.
pose S := fun T : @nonempty_metric_sets R X=>val T.
pose cost := fun T : @nonempty_metric_sets R X=>metric_real_diameter_cost c 0%R (val T).
pose nu := metric_scale_envelope S cost 1.
have hn := metric_scale_envelope_specification S cost 1.
have hmm := finite_scale_is_measure (@point_mass_is_measure R X x) hc.
have hgen T : extended_metric_diameter (S T)<=1 -> c%:E*point_mass R x (S T)<=cost T.
  move=> _; rewrite /cost /metric_real_diameter_cost metric_real_power_cost_degree_zero.
  rewrite -[X in _<=X]mule1; apply: lee_wpmul2l; first by rewrite lee_fin.
  exact: point_mass_le1.
have hl := @measure_bounded_by_metric_scale_envelope R X _ S cost 1 nu
  (fun A=>c%:E*point_mass R x A) hn hmm hgen [set x].
rewrite (@point_mass_in R X x [set x] (erefl x)) mule1 in hl.
have hlm := @caratheodory_limit_upper R X _ S cost mu hmu [set x] 1 nu ltr01 hn.
apply/eqP; rewrite eq_le hu /=; exact: le_trans hl hlm.
Qed.

(** Source for [real_power_zero_compact_subset]: degree-zero
    case of 2.10.47, p. 204, on any metric
    space. Compactness of the source is unnecessary. *)
Theorem real_power_zero_compact_subset (R : realType) (X : metricType R) c mu (A : set X) :
  is_metric_real_power_measure c 0%R mu -> (0<c)%R -> 0<mu A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hmu hc hpos.
have hm := metric_real_power_measure_law (ltW hc) hmu.
have hne : A!=set0.
  apply: contrapT=> hn.
  have he : A=set0 by apply/seteqP; split=> [x hx|x []]; apply: hn; by exists x.
  by rewrite he (measure_empty hm) ltxx in hpos.
have [x hx] := hne.
have hs := @real_power_zero_singleton R X c mu x hmu (ltW hc).
exists [set x]; split.
- exact: compact_set1.
- by move=> y ->.
- by rewrite hs lte_fin.
- by rewrite hs ltry.
Qed.
