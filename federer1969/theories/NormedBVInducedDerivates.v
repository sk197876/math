(** Federer (1969), 2.9.22, p. 167: replace the two scalar induced measures
    of 2.9.19 by the measures induced by alpha o g, for each alpha in the
    continuous dual. The quantifier over a fixed functional precedes its
    almost-everywhere assertion; no uncountable intersection of
    induced-measure exceptional sets is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  ContinuousDualUP RealFunctionalNormUP MetricLipschitzCurveVariation CurveArcLength
  NormedCurveDerivativeUP NormedDerivativeDualEvaluation RealCurveDerivativeUP
  RealBVInducedDerivativeAlternative StieltjesImageMeasures PartialFunctionUP
  MeasureDerivates ScalarIntervalDerivationContext MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_bv_scalarisation]: supporting hypothesis
    for the induced measures in Federer 2.9.22, p. 167. The
    abstract dual norm controls every scalar chain length, proving
    locally finite variation of alpha o g from that of g. Reflexivity
    and completeness are not needed for this supporting implication. *)
Lemma normed_bv_scalarisation (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> real_norm_metric_space hN) :
  curve_locally_finite_variation g -> forall a : D,
  curve_locally_finite_variation ((fun t => ed a (g t)) : R -> real_line_metric R).
Proof.
move=> hg a.
have hNa := continuous_dual_norm_laws hD a.
have h0 := real_functional_norm_nonnegative hNa.
have hbound (x y : real_norm_metric_space hN) :
    mdist (ed a x : real_line_metric R) (ed a y)<=DN a*mdist x y.
  rewrite real_line_metric_distanceE real_norm_metric_distanceE.
  rewrite -(linearB (hom_as_linear (ed a)) x y) hom_as_linearE.
  exact: real_functional_norm_bound hNa (x-y).
exact (@metric_lipschitz_curve_locally_finite_variation R
  [the metricType R of real_norm_metric_space hN] [the metricType R of real_line_metric R]
  (ed a) g (DN a) h0 hbound hg).
Qed.

(** Source for [normed_bv_scalar_induced_derivates_ae]: direct
    induced-measure alternative asserted by Federer 2.9.22, p. 167,
    extending 2.9.19(2), pp. 163–165. For each fixed alpha and
    its actual induced pair, the finite positive/negative derivates
    are the corresponding alternatives of alpha(g'), almost everywhere.
    Actual vector derivative existence is an explicit intermediate
    premise, already proved for reflexive Banach curves. *)
Theorem normed_bv_scalar_induced_derivates_ae (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> real_norm_metric_space hN)
    (a : D) (psip psim : set R -> \bar R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  is_induced_measure_pair (fun t => ed a (g t)) psip psim ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : E,
    has_normed_curve_derivative N g x v /\
    ((partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x (ed a v)%:E /\
      partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E) \/
     (partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x (-ed a v)%:E /\
      partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E))].
Proof.
move=> hg hExists hp.
have hScalarBV := @normed_bv_scalarisation R E D N hN ed DN hD g hg a.
have hScalar := @real_bv_derivative_alternative_ae R (fun t => ed a (g t)) psip psim hScalarBV hp.
have hall := measure_almost_everywhere_and (lebesgue_scalar_is_measure R) hExists hScalar.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hall)=> x [[v hv] [w [hw [_ hAlt]]]].
have hEv := @normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x v hv a.
have heq : w=ed a v := punctured_real_limit_unique hw hEv.
exists v; split=> //; by rewrite -heq.
Qed.
