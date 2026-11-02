(** Federer (1969), 2.9.21, p. 166: replace the difference of f times the
    two induced-measure derivates by f g'. The proof retains all actual
    partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  RealBVInducedDerivativeAlternative RealCurveDerivativeIntegrands WeightedRealDerivativeIntegrand
  MeasureDerivates ScalarIntervalDerivationContext LebesgueScalarMeasure MeasureAlmostUP
  MeasureAlmostBasic PartialFunctionUP PartialZeroExtension PartialDensityProduct
  PartialExtendedArithmetic PartialSimpleIntegralError SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_density_product_finite_value]: supporting finite
    multiplication for the integral calculation in Federer 2.9.21, p. 166
    Two actual finite values give their ordinary finite product, without
    changing either partial domain. *)
Lemma partial_density_product_finite_value (R : realType) (X : Type)
    (f h : partial_function X (extended_real_line R)) x (a b : R) :
  partial_function_graph f x a%:E -> partial_function_graph h x b%:E ->
  partial_function_graph (partial_density_product f h) x (a*b)%R%:E.
Proof.
move=> hf hh; apply/partial_density_product_graph; exists a%:E,b%:E.
split=> //; split=> //; by rewrite -EFinM.
Qed.

(** Source for [weighted_derivative_subset_difference_almost_equal]: direct
    almost-everywhere substitution in Federer 2.9.21, p. 166 On the common
    finite derivate region from 2.9.19, p-m=g'. Multiplying by the finite
    value f(x) and subtracting gives f g'. Off A the first factor is zero,
    while actual derivate domains remain part of the conull-set argument. *)
Lemma weighted_derivative_subset_difference_almost_equal (R : realType)
    (f g : R -> R) (psip psim : set R -> \bar R) (A : set (real_line_metric R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  let DP := @measure_derivate R [the metricType R of real_line_metric R]
    psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) in
  let DM := @measure_derivate R [the metricType R of real_line_metric R]
    psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) in
  let F := partial_function_zero_extension (0 : extended_real_line R) A (real_total_integrand f) in
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_extended_function_subtract (partial_density_product F DP) (partial_density_product F DM))
    (partial_function_zero_extension (0 : extended_real_line R) A
      (weighted_real_curve_derivative_integrand f g)).
Proof.
move=> hg hp DP DM F.
have hAlt := @real_bv_derivative_alternative_ae R g psip psim hg hp.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hAlt)=> x [v [hD [hV hCases]]].
have [p [m [hDP [hDM hpm]]]] : exists p m : R,
    partial_function_graph DP x p%:E /\ partial_function_graph DM x m%:E /\ (p-m=v)%R.
  case: hCases=> [[hpv hm0]|[hmv hp0]].
  - exists v,0%R; split=> //; split=> //; by rewrite subr0.
  - exists 0%R,(-v)%R; split=> //; split=> //; by rewrite sub0r opprK.
case: (pselect (A x))=> hAx.
- have hF : partial_function_graph F x (f x)%:E.
    apply/(partial_function_zero_extension_on _ _ _ hAx); by apply/real_total_integrand_graph.
  have hP := @partial_density_product_finite_value R (real_line_metric R) F DP x (f x) p hF hDP.
  have hM := @partial_density_product_finite_value R (real_line_metric R) F DM x (f x) m hF hDM.
  have hDiff := @partial_subtract_finite_graph R (real_line_metric R)
    (partial_density_product F DP) (partial_density_product F DM) x (f x * p)%R (f x * m)%R hP hM.
  rewrite -mulrBr hpm in hDiff.
  exists (f x*v)%R%:E; split=> //.
  apply/(partial_function_zero_extension_on _ _ _ hAx).
  apply/weighted_real_derivative_integrand_graph; by exists v; split.
- have hF : partial_function_graph F x 0.
    by apply/(partial_function_zero_extension_off _ _ _ hAx).
  have hP := @partial_density_product_finite_value R (real_line_metric R) F DP x 0 p hF hDP.
  have hM := @partial_density_product_finite_value R (real_line_metric R) F DM x 0 m hF hDM.
  rewrite mul0r in hP; rewrite mul0r in hM.
  have hDiff := @partial_subtract_finite_graph R (real_line_metric R)
    (partial_density_product F DP) (partial_density_product F DM) x 0 0 hP hM.
  rewrite subrr in hDiff; exists 0; split=> //.
  by apply/(partial_function_zero_extension_off _ _ _ hAx).
Qed.
