(** Federer (1969), 2.9.22, pp. 167–168: integrating the scalar evaluations
    of v gives alpha(g(b)-g(a)). This file proves the actual scalar integral
    identity before identifying the vector integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  RealFunctionalNormUP ContinuousDualUP PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction MeasureSubsetIntegral
  LebesgueScalarMeasure BorelFunctionBasic BorelRegularMeasureUP
  ScalarIntervalDerivationContext TopologicalBorel IntervalBumpFunctions StieltjesImageMeasures
  RealCurveDerivativeUP RealCurveDerivativeIntegrands RealAbsoluteContinuityUP
  LipschitzDualScalarisation LipschitzRealAbsoluteContinuity ReflexiveLipschitzWeakDerivative
  ReflexiveLipschitzFieldUP RestrictedIntegralIdentity MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weak_derivative_field_scalar_integral]: direct
    scalar identity in the last display of Federer 2.9.22,
    p. 167, continuing onto p. 168. The exact partial
    derivative integral from 2.9.20 is replaced by the total
    scalar evaluation of the field only on their proved
    common conull set. The target interval remains closed. *)
Theorem weak_derivative_field_scalar_integral (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g v : R -> E) (L a b : R) :
  0<=L -> (forall t u, N (g t-g u)<=L * `|t-u|) ->
  is_bounded_weak_derivative_field hN ed (@lebesgue_scalar_measure R) g v L -> a<b ->
  forall alpha : D, is_measure_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (partial_function_total (fun x => ((ed alpha (v x))%:E : extended_real_line R)))
    (ed alpha (g b-g a))%:E.
Proof.
move=> hL hg hv hab alpha.
have hm := lebesgue_scalar_is_measure R.
have hDa := real_functional_norm_nonnegative (continuous_dual_norm_laws hD alpha).
have hs := @normed_lipschitz_scalarisation R E D N hN ed DN hD g L hg alpha.
have hi := @lipschitz_real_derivative_integral_increment R
  (fun t => ed alpha (g t)) (DN alpha * L) a b (mulr_ge0 hDa hL) hs hab.
have hI := hi b (ltW hab) (lexx b).
have hA : measure_measurable (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)).
  exact (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R)
    _ (closed_borel_set (@segment_closed_real R a b))).
have hrestricted := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[a,b] _ _ hA).2 hI.
have he : measure_almost_equal
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (real_curve_derivative_integrand (fun t => ed alpha (g t)))
    (partial_function_total (fun x => ((ed alpha (v x))%:E : extended_real_line R))).
  have hweak := bounded_weak_field_scalar_derivatives hv.
  have hAE : measure_almost_everywhere (@lebesgue_scalar_measure R)
      (partial_function_agreement
        (real_curve_derivative_integrand (fun t => ed alpha (g t)))
        (partial_function_total (fun x => ((ed alpha (v x))%:E : extended_real_line R)))).
    apply: (@measure_almost_everywhere_mono R (real_line_metric R)
      (@lebesgue_scalar_measure R) hm _ _ _ hweak)=> x hx.
    exists (ed alpha (v x))%:E; split=> //.
    by exists (ed alpha (v x)); split=> //; exact: hx alpha.
  apply: (@measure_null_subset R (real_line_metric R) (@lebesgue_scalar_measure R)
    hm _ _ _ hAE)=> x [_ hx]; exact hx.
rewrite (linearB (hom_as_linear (ed alpha)) (g b) (g a)) !hom_as_linearE.
exact (@measure_integral_almost_equal R (real_line_metric R)
  (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
  (measure_restrict_is_measure hm `[a,b]) _ _ _ hrestricted he).
Qed.
