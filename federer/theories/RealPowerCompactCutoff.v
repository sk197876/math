(** Federer (1969), 2.10.47, p. 205: apply compact-cost continuity to the
    original real power cutoffs. The equality of compact and unrestricted
    finite-cutoff infima transfers the full abstract laws, not just one
    numerical bound. Source context: RealPowerCompactCost.v and
    RealPowerCompactScaleAgreement.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile HausdorffLengthUP LipschitzFunctionCompact
  MetricRealPowerCost RealPowerCompactCost RealPowerCompactScaleAgreement
  MetricScaleEnvelopeUP MetricScaleEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_compact_cutoff_laws]: supporting
    transfer of finite-cutoff laws for the invocation
    of 2.10.20 in 2.10.47, p. 205.
    Compact costs are finite real numbers; no new
    cover regularity is assumed. *)
Theorem real_power_compact_cutoff_laws (R : realType) (X : metricType R)
    (c p d : R) (nu : set X -> \bar R) :
  metric_boundedly_compact X -> (0<=c)%R -> (0<=d)%R ->
  is_metric_scale_envelope (fun S : @nonempty_metric_sets R X=>val S)
    (fun S=>metric_real_diameter_cost c p (val S)) d%:E nu ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C)
    (fun C=>(real_power_compact_generator_cost c p C)%:E) d%:E nu.
Proof.
move=> hX hc hd hn.
pose eta := metric_scale_envelope (fun C : compact_metric_set X=>val C)
  (fun C=>(real_power_compact_generator_cost c p C)%:E) d%:E.
have he : (fun C : compact_metric_set X=>metric_real_diameter_cost c p (val C))=
    (fun C : compact_metric_set X=>(real_power_compact_generator_cost c p C)%:E).
  apply: funext=> C; exact: real_power_compact_generator_cost_value.
have hspec := metric_scale_envelope_specification (fun C : compact_metric_set X=>val C)
  (fun C=>(real_power_compact_generator_cost c p C)%:E) d%:E.
have hraw : is_metric_scale_envelope (fun C : compact_metric_set X=>val C)
    (fun C=>metric_real_diameter_cost c p (val C)) d%:E eta by rewrite he.
have hsame : nu=eta.
  apply: funext=> A; exact: (@real_power_compact_scale_agreement R X c p d nu eta hX hc hd hn hraw A).
by rewrite hsame.
Qed.
