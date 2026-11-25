(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactHausdorffMetric RealMetricBackground CompactGeneratorCostUP CompactSetDistanceProfile LipschitzFunctionCompact HausdorffLengthUP MetricRealPowerCost RealPowerCompactCost RealPowerCompactCutoff MetricRealPowerMeasureUP MetricScaleEnvelope MetricScaleEnvelopeLaws CaratheodoryLimitUP CaratheodoryBorelRegular RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_compact_cost_nonnegative_degree]: supporting
    2.10.48, p. 206, by verifying the compact-cost hypotheses
    of 2.10.23, p. 186, for the power gauges. Degree zero has constant positive
    cost, so it is included without a singleton exception. *)
Lemma real_power_compact_cost_nonnegative_degree (R : realType) (X : metricType R) c p :
  (0<c)%R -> (0<=p)%R ->
  is_continuous_positive_compact_cost (@real_power_compact_generator_cost R X c p).
Proof.
move=> hc hp; case: (eqVneq p 0%R)=> [->|hne].
- have he : (@real_power_compact_generator_cost R X c 0)=fun _=>c.
    apply: funext=> C; by rewrite /real_power_compact_generator_cost real_power_zero_exponent mulr1.
  rewrite he; constructor.
  + move=> C; exact: ltW hc.
  + move=> C; exact (@cvg_cst (real_line_metric R) c (compact_hausdorff_space X) (nbhs C) (nbhs_filter C)).
  + by move=> C _.
- apply: real_power_compact_generator_cost_laws hc _.
  by rewrite lt_neqAle eq_sym hne hp.
Qed.

(** Source for [real_power_compact_limit_laws]: supporting transfer
    from unrestricted to compact generators in 2.10.48, p. 206,
    as in the Hausdorff application of 2.10.24, p. 188.
    Finite positive cutoffs are cofinal, including below infinity. *)
Theorem real_power_compact_limit_laws (R : realType) (X : metricType R) c p
    (mu : set X -> \bar R) :
  metric_boundedly_compact X -> (0<=c)%R -> is_metric_real_power_measure c p mu ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C)
    (fun C=>(real_power_compact_generator_cost c p C)%:E) mu.
Proof.
move=> hX hc hmu.
pose G := fun S : @nonempty_metric_sets R X=>val S.
pose cost := fun S : @nonempty_metric_sets R X=>metric_real_diameter_cost c p (val S).
pose H := fun C : compact_metric_set X=>val C.
pose cc := fun C : compact_metric_set X=>(real_power_compact_generator_cost c p C)%:E.
constructor.
- move=> A delta nu hd hn.
  have [k hk] := reciprocal_metric_cutoffs_cofinal hd.
  pose d : R := ((k.+1%:R)^-1)%R.
  have hd0 : (0<d)%R by rewrite /d invr_gt0 ltr0n.
  have hdE : 0<d%:E by rewrite lte_fin.
  have hs := metric_scale_envelope_specification G cost d%:E.
  have ht := @real_power_compact_cutoff_laws R X c p d _ hX hc (ltW hd0) hs.
  apply: le_trans (@metric_scale_envelope_antitone_cutoff R X _ H cc d%:E delta _ nu ht hn hk A) _.
  exact: (@caratheodory_limit_upper R X _ G cost mu hmu A d%:E _ hdE hs).
- move=> A b hb; apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
  have [k hk] := reciprocal_metric_cutoffs_cofinal hd.
  pose d : R := ((k.+1%:R)^-1)%R.
  have hd0 : (0<d)%R by rewrite /d invr_gt0 ltr0n.
  have hdE : 0<d%:E by rewrite lte_fin.
  have hs := metric_scale_envelope_specification G cost d%:E.
  have ht := @real_power_compact_cutoff_laws R X c p d _ hX hc (ltW hd0) hs.
  apply: le_trans (@metric_scale_envelope_antitone_cutoff R X _ G cost d%:E delta _ nu hs hn hk A) _.
  exact: hb _ _ hdE ht.
Qed.
