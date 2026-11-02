(** Federer (1969), 2.10.47, p. 205: transfer the final compact-cutoff
    inequality to real power gauges. At each finite cutoff in a boundedly
    compact space, closures turn arbitrary nonempty generators into compact
    generators without changing diameter or cost. This is the same argument
    as the Hausdorff application of 2.10.24, p. 188, with coefficient and
    real degree explicit. Source context: RealPowerCompactCost.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffLengthUP CompactSetDistanceProfile MetricDiameter MetricDiameterClosure
  MetricRealPowerCost HausdorffCompactScaleAgreement MetricScaleEnvelopeUP MetricScaleCutoffCost
  MetricScaleWeightedBound MetricScaleMeasureBound MeasureUP MeasureBasic LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_compact_scale_agreement]: supporting
    equality of finite-cutoff covering infima needed in
    2.10.47, p. 205. The gauge coefficient is
    nonnegative; no condition on the exponent is needed
    for this closure-invariance argument. *)
Theorem real_power_compact_scale_agreement (R : realType) (X : metricType R) (c p : R) (d : R)
    (nu xi : set X -> \bar R) :
  metric_boundedly_compact X -> (0<=c)%R -> (0<=d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) d%:E nu ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C)
    (fun C=>metric_real_diameter_cost c p (val C)) d%:E xi ->
  forall A, nu A=xi A.
Proof.
move=> hX hc hd hn hxi A.
have hcost (S : set X) : 0<=metric_real_diameter_cost c p S := @metric_real_power_cost_nonnegative R c p (extended_metric_diameter S) hc.
have hnm := metric_scale_envelope_is_measure hn (fun j=>hcost (val j)).
have hxm := metric_scale_envelope_is_measure hxi (fun C=>hcost (val C)).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@measure_bounded_by_metric_scale_envelope R X (compact_metric_set X) (fun C=>val C)
    (fun C=>metric_real_diameter_cost c p (val C)) d%:E xi nu hxi hnm)=> C hCd.
  pose j : @nonempty_metric_sets R X := exist _ (val C) (mem_set (set_valP C).2).
  exact: (@metric_scale_generator_bound R X (@nonempty_metric_sets R X) (fun j=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) d%:E nu j hn (hcost (val j)) hCd).
- apply: (@measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X) (fun j=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) d%:E nu xi hn hxm)=> j hjd.
  have hcomp := @finite_diameter_closure_compact R X (val j) d hX (set_valP j) hd hjd.
  have hne : closure (val j)!=set0 by have [x hx] := set_valP j; exists x; exact: subset_closure hx.
  pose C : compact_metric_set X := exist _ (closure (val j)) (mem_set (conj hcomp hne)).
  have hCd : extended_metric_diameter (val C)<=d%:E by rewrite /= extended_metric_diameter_closure.
  have hh := @metric_scale_generator_bound R X (compact_metric_set X) (fun C=>val C)
    (fun C=>metric_real_diameter_cost c p (val C)) d%:E xi C hxi (hcost (val C)) hCd.
  change (is_true (xi (closure (val j))<=metric_real_diameter_cost c p (closure (val j)))) in hh.
  rewrite metric_real_diameter_cost_closure in hh; apply: le_trans _ hh.
  apply: (@measure_mono R X xi hxm)=> x hx; exact: subset_closure hx.
Qed.
