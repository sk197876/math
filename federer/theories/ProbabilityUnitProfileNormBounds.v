(** Supporting Federer (1969), 3.2.45, p. 279:
    uniform positive finite norm bounds for normalized profiles,
    from the probability norm comparison of 2.4.17, p. 90. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasureBasic
  MeasurableFunctionUP MeasureExponentDomain MeasureEssentialNormUP MeasureEssentialNorm MeasureGauge
  ProbabilityExponentMonotone MeasureReciprocalInterval ReciprocalExponent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_unit_profile_norm_bounds]: expanded
    norm-domain helper for Federer 3.2.45, p. 279. A common
    positive lower bound at exponent one and a pointwise unit
    upper bound give the same bounds at every exponent,
    including infinity, by 2.4.17, p. 90. *)
Theorem probability_unit_profile_norm_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hMu : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (d : R) :
  mu setT = 1 -> (0 < d)%R -> (forall x, (`|f x| <= 1)%R) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  d%:E <= measure_exponent_norm mu (partial_function_total f) 1 ->
  forall t, 1 <= t ->
    d%:E <= measure_exponent_norm mu (partial_function_total f) t /\
    measure_exponent_norm mu (partial_function_total f) t <= 1.
Proof.
move=> hProbability hD hUnit hF hLower t hT.
have hUpper : measure_exponent_norm mu (partial_function_total f) +oo <= 1.
  apply: measure_essential_norm_bound; split; first exact: ler01.
  have hEmpty : partial_norm_superlevel (fun y : R => `|y|%R)
      (partial_function_total f) (1 : \bar R) = set0.
    apply/seteqP; split=> x; last by [].
    move=> [y [hy hLarge]].
    have hValue : f x = y := hy.
    have h : (1 < `|y|)%R := hLarge.
    rewrite -hValue in h.
    by have := lt_le_trans h (hUnit x); rewrite ltxx.
  by rewrite hEmpty (measure_empty hMu).
split.
- apply: le_trans hLower _.
  exact: (@probability_measure_exponent_norm_monotone R X mu hMu _ 1 t
    hProbability (lexx 1) hT hF).
- apply: le_trans _ hUpper.
  exact: (@probability_measure_exponent_norm_monotone R X mu hMu _ t +oo
    hProbability hT (leey t) hF).
Qed.

(** Source for [probability_unit_profile_reciprocal_domain]:
    expanded identification of the original positive finite
    reciprocal-norm domain in 2.4.17, p. 90, for the
    normalized profiles used in Federer 3.2.45, p. 279.
    The whole closed reciprocal interval is retained. *)
Corollary probability_unit_profile_reciprocal_domain (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hMu : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (d : R) :
  mu setT = 1 -> (0 < d)%R -> (forall x, (`|f x| <= 1)%R) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  d%:E <= measure_exponent_norm mu (partial_function_total f) 1 ->
  measure_positive_reciprocal_exponents mu (partial_function_total f) =
    [set u : R | (0 <= u <= 1)%R].
Proof.
move=> hProbability hD hUnit hF hLower.
apply/seteqP; split=> u.
- move=> [hU [hU1 _]]; by apply/andP; split.
- move=> /andP[hU hU1].
  have hExponent := @reciprocal_lebesgue_exponent_domain R u hU hU1.
  have [hLo hHi] := @probability_unit_profile_norm_bounds R X mu hMu f d
    hProbability hD hUnit hF hLower _ hExponent.
  split=> //; split=> //; rewrite measure_reciprocal_exponent_normE; split.
  + exact: lt_le_trans (lte_tofin hD) hLo.
  + exact: le_lt_trans hHi (ltry 1%R).
Qed.
