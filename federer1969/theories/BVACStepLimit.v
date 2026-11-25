(** Federer (1969), 2.9.24, p. 169: bounded convergence identifies the limit
    of the finite step integrals. This supporting theorem uses globally
    defined proof representatives: f is bounded and BV, and g is continuous,
    BV and absolutely continuous on [a,b]. The printed local hypotheses will
    provide exactly these representatives by retraction. The local Federer
    erratum has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealMetricCompleteness CurveArcLength
  BVCurveBorel BVCurveMeasurable MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP LebesgueScalarMeasure TotalScalarLpUP TotalScalarMeasurability
  TotalScalarCutoff RealAbsoluteContinuityUP RealDerivativeRepresentative
  ACDerivativePrimitiveDensity RightStepApproximation RightStepSupport
  RightStepIntegralValues UniformStieltjesSumLimit BoundedWeightedIntegralLimit
  StieltjesIntegral StieltjesSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bv_ac_step_integral_limit]: supporting complete
    limit passage in Federer 2.9.24, p. 169. Its hypotheses
    concern the retracted proof representatives; no continuity
    of f is required. The conclusion is an actual integral
    of the cutoff derivative density with the printed boundary value. *)
Theorem bv_ac_step_integral_limit (R : realType) (f g : R -> R) (a b M : R) :
  curve_locally_finite_variation (f : R -> real_line_metric R) ->
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  continuous (g : real_line_metric R -> real_line_metric R) ->
  a<b -> is_absolutely_continuous_real_curve g a b ->
  0<=M -> (forall x : R, `|f x|<=M) ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => f x*
      total_scalar_cutoff (`[a,b] : set R) (real_derivative_representative g) x))
    (f b*g b-f a*g a-stieltjes_integral f g a b)%:E.
Proof.
move=> hf hg hgc hab hAC hM hfb.
have hm := lebesgue_scalar_is_measure R.
pose q := total_scalar_cutoff (`[a,b] : set R) (real_derivative_representative g).
have hcell := @absolutely_continuous_derivative_primitive_density R g a b hg hab hAC.
have hAB := hcell a b (lexx _) (ltW hab) (lexx _).
have hqI : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand q) (g b-g a)%:E.
  exact: measure_integral_graph_equivalent (total_scalar_cutoff_integrand_graph _ _) hAB.
have hq : summable_real_functions (@lebesgue_scalar_measure R) q by exists (g b-g a).
have hFbor := @complete_metric_bv_curve_borel R [the metricType R of real_line_metric R]
  f (@real_line_metric_complete R) hf.
have hFline := @borel_map_measure_measurable R [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] (@lebesgue_scalar_measure R) f hm
  (lebesgue_scalar_borel_regular R) hFbor.
have hFscalar := @real_total_scalar_measurable R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm f hFline.
have hbound (n : nat) (x : R) : `|uniform_right_step_approximation f a b n x|<=M.
  apply: (@uniform_right_step_bound R f a b M (ltW hab) hM) => t _ _.
  exact: hfb t.
have hAE := @bv_right_step_cutoff_almost_limit R f (real_derivative_representative g)
  a b hf (ltW hab).
have hvalues (n : nat) : is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => uniform_right_step_approximation f a b n x*q x))
    (f b*g b-f a*g a-stieltjes_sum g f (uniform_partition a b n))%:E.
  have hi := @right_step_integration_by_parts_integral R f g a b hg hab hAC n.
  by rewrite (@uniform_right_step_cutoff_product R f (real_derivative_representative g)
    a b (ltW hab) n) in hi.
have hlimit := @right_step_integral_values_limit R f g a b hf hgc (ltW hab).
exact (@bounded_weighted_integral_limit R (real_line_metric R) (@lebesgue_scalar_measure R) hm
  (uniform_right_step_approximation f a b) f q M
  (fun n => f b*g b-f a*g a-stieltjes_sum g f (uniform_partition a b n))
  (f b*g b-f a*g a-stieltjes_integral f g a b)
  hq hFscalar hM hfb hbound hAE hvalues hlimit).
Qed.
