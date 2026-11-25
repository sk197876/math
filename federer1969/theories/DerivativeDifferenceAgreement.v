(** Federer (1969), 2.9.20, p. 166: replace D(psi+)-D(psi-) by g' in the
    derivative integral. All partial domains and zero extensions are
    retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  RealBVInducedDerivativeAlternative RealCurveDerivativeIntegrands MeasureDerivates
  ScalarIntervalDerivationContext LebesgueScalarMeasure MeasureAlmostUP MeasureAlmostBasic
  PartialFunctionUP PartialZeroExtension PartialExtendedArithmetic PartialSimpleIntegralError
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivative_subset_difference_almost_equal]: direct
    almost-everywhere substitution in the last calculation of Federer
    2.9.20, p. 166 Both alternatives of 2.9.19 yield D(psi+)-D(psi-)=g' with
    finite values before subtraction. Off the target set all three zero
    extensions are zero. The set A need not be measurable for this agreement
    lemma. *)
Lemma derivative_subset_difference_almost_equal (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (A : set (real_line_metric R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  let DP := @measure_derivate R [the metricType R of real_line_metric R]
    psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) in
  let DM := @measure_derivate R [the metricType R of real_line_metric R]
    psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) in
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_extended_function_subtract
      (partial_function_zero_extension (0 : extended_real_line R) A DP)
      (partial_function_zero_extension (0 : extended_real_line R) A DM))
    (partial_function_zero_extension (0 : extended_real_line R) A
      (real_curve_derivative_integrand g)).
Proof.
move=> hg hp DP DM; have hm := lebesgue_scalar_is_measure R.
have hAlt := @real_bv_derivative_alternative_ae R g psip psim hg hp.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hAlt)=> x [v [hG [hV hCases]]].
pose F := partial_function_zero_extension (0 : extended_real_line R) A DP.
pose G := partial_function_zero_extension (0 : extended_real_line R) A DM.
pose Q := real_curve_derivative_integrand g.
case: (pselect (A x))=> hAx.
- have hQ : partial_function_graph Q x v%:E by exists v; split.
  have hZ := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
    0 A Q x v%:E hAx).2 hQ.
  exists v%:E; split; last exact hZ.
  case: hCases=> [[hDp hDm]|[hDm hDp]].
  + have hF := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DP x v%:E hAx).2 hDp.
    have hG0 := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DM x 0 hAx).2 hDm.
    have hD := @partial_subtract_finite_graph R (real_line_metric R) F G x v 0 hF hG0.
    by rewrite subr0 in hD.
  + have hF0 := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DP x 0 hAx).2 hDp.
    have hGminus := (@partial_function_zero_extension_on (real_line_metric R) (extended_real_line R)
      0 A DM x (-v)%:E hAx).2 hDm.
    have hD := @partial_subtract_finite_graph R (real_line_metric R) F G x 0 (-v) hF0 hGminus.
    by rewrite sub0r opprK in hD.
- have hF0 := (@partial_function_zero_extension_off (real_line_metric R) (extended_real_line R)
    0 A DP x 0 hAx).2 erefl.
  have hG0 := (@partial_function_zero_extension_off (real_line_metric R) (extended_real_line R)
    0 A DM x 0 hAx).2 erefl.
  have hZ0 := (@partial_function_zero_extension_off (real_line_metric R) (extended_real_line R)
    0 A Q x 0 hAx).2 erefl.
  exists 0; split; last exact hZ0.
  have hD := @partial_subtract_finite_graph R (real_line_metric R) F G x 0 0 hF0 hG0.
  by rewrite subrr in hD.
Qed.
