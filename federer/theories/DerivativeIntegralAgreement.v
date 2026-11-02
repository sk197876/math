(** Federer (1969), 2.9.19, p. 165: replace the sum of the two
    induced-measure derivates by |g'| in the integral. All functions retain
    their partial domains, and the subset integrands are formed through the
    sealed zero- extension laws of 2.4.10. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  StieltjesDerivationClass RealBVInducedDerivativeAlternative RealCurveDerivativeUP
  RealCurveDerivativeIntegrands MeasureDerivationContext DerivationLevelSeparation
  MeasureAlmostUP MeasureAlmostBasic MeasureUP LebesgueScalarMeasure
  MeasureDerivates ScalarIntervalDerivationContext PartialFunctionUP PartialZeroExtension
  PartialExtendedArithmetic ExtendedRealOrderTopology ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivative_subset_sum_almost_equal]: direct
    almost-everywhere replacement in the final calculation of Federer
    2.9.19, p. 165 On each side of the measure-derivate alternative, the sum
    equals the finite |g'|. Outside A, both subset integrands are zero by
    their laws. A may be arbitrary for this agreement lemma; integrability
    later requires its measurability. *)
Lemma derivative_subset_sum_almost_equal (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (A : set (real_line_metric R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  let DP := @measure_derivate R [the metricType R of real_line_metric R]
    psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) in
  let DM := @measure_derivate R [the metricType R of real_line_metric R]
    psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) in
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_extended_function_add
      (partial_function_zero_extension (0 : extended_real_line R) A DP)
      (partial_function_zero_extension (0 : extended_real_line R) A DM))
    (partial_function_zero_extension (0 : extended_real_line R) A
      (real_curve_absolute_derivative_integrand g)).
Proof.
move=> hg hp DP DM.
have hm := lebesgue_scalar_is_measure R.
have [hCP hCM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hCP; have hmM := derivation_measure_law hCM.
have hAlt := @real_bv_derivative_alternative_ae R g psip psim hg hp.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hAlt).
move=> x [v [hG [hV hCases]]].
pose F := partial_function_zero_extension (0 : extended_real_line R) A DP.
pose G := partial_function_zero_extension (0 : extended_real_line R) A DM.
pose Q := real_curve_absolute_derivative_integrand g.
pose Z := partial_function_zero_extension (0 : extended_real_line R) A Q.
case: (pselect (A x))=> hAx.
- have hAbs : partial_function_graph Q x `|v|%:E by exists v; split.
  have hZ := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
    0 A Q x `|v|%:E hAx).2 hAbs.
  exists `|v|%:E; split; last exact hZ.
  apply/partial_extended_function_add_graph.
  case: hCases=> [[hDp hDm]|[hDm hDp]].
  + have hpos := @measure_derivate_value_nonnegative R [the metricType R of real_line_metric R]
      (@lebesgue_scalar_measure R) psip (@scalar_nondegenerate_interval_relation R) x v%:E hm hmP hDp.
    have hv : (0<=v)%R by move: hpos; rewrite lee_fin.
    have hF := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DP x v%:E hAx).2 hDp.
    have hG0 := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DM x 0 hAx).2 hDm.
    exists v%:E,0; split; first exact hF.
    split; first exact hG0.
    by rewrite (ger0_norm hv) /extended_add /= addr0.
  + have hpos := @measure_derivate_value_nonnegative R [the metricType R of real_line_metric R]
      (@lebesgue_scalar_measure R) psim (@scalar_nondegenerate_interval_relation R) x (-v)%:E hm hmM hDm.
    have hv : (v<=0)%R by move: hpos; rewrite lee_fin oppr_ge0.
    have hF0 := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DP x 0 hAx).2 hDp.
    have hGminus := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DM x (-v)%:E hAx).2 hDm.
    exists 0,(-v)%:E; split; first exact hF0.
    split; first exact hGminus.
    by rewrite (ler0_norm hv) /extended_add /= add0r.
- have hF0 := (@partial_function_zero_extension_off (real_line_metric R) (extended_real_line R)
    0 A DP x 0 hAx).2 erefl.
  have hG0 := (@partial_function_zero_extension_off (real_line_metric R) (extended_real_line R)
    0 A DM x 0 hAx).2 erefl.
  have hZ0 := (@partial_function_zero_extension_off (real_line_metric R) (extended_real_line R)
    0 A Q x 0 hAx).2 erefl.
  exists 0; split; last exact hZ0.
  apply/partial_extended_function_add_graph; exists 0,0.
  split; first exact hF0.
  split; first exact hG0.
  by rewrite /extended_add /= addr0.
Qed.
