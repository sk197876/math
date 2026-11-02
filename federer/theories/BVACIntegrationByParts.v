(** Federer (1969), 2.9.24, p. 169: after bounded convergence, restore the
    actual partial integrand f g'. This intermediate theorem concerns the
    globally defined retracted proof representatives; the final theorem
    removes those auxiliary global hypotheses. The local Federer erratum has
    no entry for this formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension CurveArcLength MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  MeasureSubsetIntegral MeasureDensityTransfer SummableRealFunctionUP TotalScalarCutoff
  LebesgueScalarMeasure RealAbsoluteContinuityUP RealDerivativeRepresentative
  WeightedRealDerivativeIntegrand StieltjesIntegral BVACStepLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_bv_ac_integration_by_parts]: supporting
    integration-by-parts formula for the retracted representatives
    in Federer 2.9.24, p. 169. The derivative is again
    the exact partial derivative; no representative values are
    assigned at points where it is undefined. *)
Theorem bounded_bv_ac_integration_by_parts (R : realType) (f g : R -> R) (a b M : R) :
  curve_locally_finite_variation (f : R -> real_line_metric R) ->
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  continuous (g : real_line_metric R -> real_line_metric R) ->
  a<b -> is_absolutely_continuous_real_curve g a b ->
  0<=M -> (forall x : R, `|f x|<=M) ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand f g)
    (f b*g b-f a*g a-stieltjes_integral f g a b)%:E.
Proof.
move=> hf hg hgc hab hAC hM hfb.
have hm := lebesgue_scalar_is_measure R.
have hi := @bv_ac_step_integral_limit R f g a b M hf hg hgc hab hAC hM hfb.
have hprod : (fun x => f x*total_scalar_cutoff (`[a,b] : set R)
    (real_derivative_representative g) x)=
    total_scalar_cutoff (`[a,b] : set R) (fun x => f x*real_derivative_representative g x).
  apply: funext=> x; by rewrite /total_scalar_cutoff mulrA.
rewrite hprod in hi.
have hsub : is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand (fun x => f x*real_derivative_representative g x))
    (f b*g b-f a*g a-stieltjes_integral f g a b)%:E.
  apply: (@measure_integral_graph_equivalent R (real_line_metric R) _ _ _ _ _ hi)=> x z.
  symmetry; exact: total_scalar_cutoff_integrand_graph.
have hD := bv_real_derivative_representative_ae hg.
have hAE : measure_almost_equal (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => f x*real_derivative_representative g x))
    (weighted_real_curve_derivative_integrand f g).
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) _ hm _ _ _ hD)=> x hx.
  exists (f x*real_derivative_representative g x)%:E; split.
  - by apply/real_total_integrand_graph.
  - apply/weighted_real_derivative_integrand_graph.
    by exists (real_derivative_representative g x); split.
have hAEsub := @zero_extension_almost_equal R (real_line_metric R) (extended_real_line R)
  (@lebesgue_scalar_measure R) hm 0 `[a,b] _ _ hAE.
exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hsub hAEsub).
Qed.
