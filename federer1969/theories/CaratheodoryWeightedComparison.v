(** Supporting weighted comparison for Federer (1969), 2.10.5, p. 173:
    monotonicity of beta_t I_t and beta_t Q_t follows from comparison of
    their normalized generator costs. Expand this consequence of the
    covering infimum and supremum laws in 2.10.1, p. 170. At a common
    cutoff, compare the preliminary measures through the existing weighted
    generator bound, then pass to the final supremum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import CaratheodoryLimitUP MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleCutoffCost MetricScaleWeightedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_weighted_generator_comparison]:
    supporting weighted cost comparison for the
    normalized-measure assertion in Federer
    2.10.5, p. 173. A positive finite
    factor multiplying every target cost also
    bounds the corresponding final measure. *)
Theorem caratheodory_weighted_generator_comparison (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c d : J -> \bar R)
    (mu nu : set X -> \bar R) (a : R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit S d nu ->
  (forall j, 0<=c j) -> (forall j, 0<=d j) -> (0<a)%R ->
  (forall j, c j<=a%:E*d j) -> forall A, mu A<=a%:E*nu A.
Proof.
move=> hm hn hc hd ha hcost A; apply: (caratheodory_limit_least hm)=> delta xi hdelta hxi.
pose eta := metric_scale_envelope S d delta.
have heta := @metric_scale_envelope_specification R X J S d delta.
have hxim := @metric_scale_envelope_is_measure R X J S c delta xi hxi hc.
have hbound : xi A<=a%:E*eta A.
  apply: (@measure_bounded_by_scaled_metric_envelope R X J S d delta eta xi a heta hxim ha)=> j hj.
  exact: le_trans (@metric_scale_generator_bound R X J S c delta xi j hxi (hc j) hj) (hcost j).
apply: le_trans hbound _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW ha.
exact: (@caratheodory_limit_upper R X J S d nu hn A delta eta hdelta heta).
Qed.

(** Source for [caratheodory_normalized_cost_comparison]:
    supporting comparison of two independently
    normalized constructions in Federer 2.10.5,
    p. 173. Positive finite normalizers are
    multiplied back after the weighted comparison,
    including infinite final measure values. *)
Theorem caratheodory_normalized_cost_comparison (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c d : J -> \bar R)
    (mu nu : set X -> \bar R) (a b : R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit S d nu ->
  (forall j, 0<=c j) -> (forall j, 0<=d j) -> (0<a)%R -> (0<b)%R ->
  (forall j, a%:E*c j<=b%:E*d j) -> forall A, a%:E*mu A<=b%:E*nu A.
Proof.
move=> hm hn hc hd ha hb hcost A.
have han : a!=0%R by rewrite gt_eqF.
have hr : (0<b/a)%R by rewrite divr_gt0.
have hcomp j : c j<=(b/a)%R%:E*d j.
  have hai : 0<=(a^-1)%R%:E by rewrite lee_fin invr_ge0; exact: ltW ha.
  have h := lee_wpmul2l hai (hcost j).
  rewrite !muleA -!EFinM mulVf // mul1e in h.
  by rewrite mulrC in h.
have hh := @caratheodory_weighted_generator_comparison R X J S c d mu nu (b/a)%R
  hm hn hc hd hr hcomp A.
have haE : 0<=a%:E by rewrite lee_fin; exact: ltW ha.
have h := lee_wpmul2l haE hh.
have he : (a*(b/a))%R=b by rewrite mulrC divfK.
by rewrite muleA -EFinM he in h.
Qed.
