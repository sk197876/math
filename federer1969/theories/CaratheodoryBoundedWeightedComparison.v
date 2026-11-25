(** Supporting Federer (1969), 3.2.45, p. 279: uniform cost
    comparisons need only the bounded generators that occur at
    finite cutoffs in the construction of 2.10.1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import CoveringFamilyUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleCutoffCost MetricScaleWeightedBound CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_bounded_weighted_generator_comparison]:
    expanded finite-cutoff helper for the comparison of Q_t in
    Federer 3.2.45, p. 279, by the infimum and supremum laws
    of 2.10.1, p. 170. A positive finite uniform multiplier
    on all bounded generators bounds the final outer measures.
    Arbitrary target sets and infinite measure values are retained. *)
Theorem caratheodory_bounded_weighted_generator_comparison (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c d : J -> \bar R)
    (mu nu : set X -> \bar R) (a : R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit S d nu ->
  (forall j, 0 <= c j) -> (0 < a)%R ->
  (forall j, metric_set_bounded (S j) -> c j <= a%:E*d j) ->
  forall A, mu A <= a%:E*nu A.
Proof.
move=> hMu hNu hC hA hCost A.
apply: (caratheodory_limit_least hMu)=> delta xi hDelta hXi.
have [ell hCutoff] := reciprocal_metric_cutoffs_cofinal hDelta.
pose e : R := (((ell.+1)%:R)^-1)%R.
have he : (0 < e)%R by rewrite /e invr_gt0 ltr0n.
pose eta := metric_scale_envelope S d e%:E.
have hEta := @metric_scale_envelope_specification R X J S d e%:E.
have hXiMeasure := metric_scale_envelope_is_measure hXi hC.
have hGenerator j : extended_metric_diameter (S j) <= e%:E -> xi (S j) <= a%:E*d j.
  move=> hSize.
  have hBound : metric_set_bounded (S j) := le_lt_trans hSize (ltry e).
  apply: le_trans (@metric_scale_generator_bound R X J S c delta xi j hXi (hC j)
    (le_trans hSize hCutoff)) _.
  exact: hCost.
have hBound := @measure_bounded_by_scaled_metric_envelope R X J S d e%:E eta xi a
  hEta hXiMeasure hA hGenerator A.
apply: le_trans hBound _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW hA.
exact: (@caratheodory_limit_upper R X J S d nu hNu A e%:E eta he hEta).
Qed.

(** Source for [caratheodory_bounded_normalized_cost_comparison]:
    expanded normalized-cost helper for Federer 3.2.45, p. 279.
    Two positive finite normalizers may be multiplied back after
    comparing only bounded generators. No division by an infinite
    final measure or new covering choice is introduced. *)
Corollary caratheodory_bounded_normalized_cost_comparison (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c d : J -> \bar R)
    (mu nu : set X -> \bar R) (a b : R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit S d nu ->
  (forall j, 0 <= c j) -> (0 < a)%R -> (0 < b)%R ->
  (forall j, metric_set_bounded (S j) -> a%:E*c j <= b%:E*d j) ->
  forall A, a%:E*mu A <= b%:E*nu A.
Proof.
move=> hMu hNu hC hA hB hCost A.
have hANe : a != 0%R := lt0r_neq0 hA.
have hRatio : (0 < b/a)%R := divr_gt0 hB hA.
have hGenerator j (hBound : metric_set_bounded (S j)) : c j <= (b/a)%R%:E*d j.
  have hInverse : 0 <= (a^-1)%R%:E by rewrite lee_fin invr_ge0; exact: ltW hA.
  have h := lee_wpmul2l hInverse (hCost j hBound).
  rewrite !muleA -!EFinM mulVf // mul1e in h.
  by rewrite mulrC in h.
have h := @caratheodory_bounded_weighted_generator_comparison R X J S c d mu nu (b/a)%R
  hMu hNu hC hRatio hGenerator A.
have hScaled := lee_wpmul2l (lee_tofin (ltW hA)) h.
have hEquality : (a*(b/a)=b)%R by rewrite mulrC divfK.
by rewrite muleA -EFinM hEquality in hScaled.
Qed.
