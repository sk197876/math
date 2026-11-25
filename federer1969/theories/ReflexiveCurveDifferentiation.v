(** Federer (1969), 2.9.22, pp. 167–168: the complete extension of
    2.9.19–2.9.20 to locally BV curves in a reflexive Banach space. The
    actual norm derivative, its scalar dual characterisation, variation
    quotient, norm-integral estimate, scalar induced-measure alternatives
    and all four absolute- continuity conditions are assembled below. Source
    comments in the supporting modules expand the printed proof and
    distinguish the diameter-cover null-transfer route from Federer's
    open-set argument. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP CurveArcLength CurveVariationUP
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands NormedCurveAbsoluteContinuityUP
  MetricCurveAbsoluteContinuityUP NormedBVDerivativeIntegral NormedBVInducedDerivates
  NormedBVVariationDerivative ReflexiveBVDifferentiation NormedAbsoluteContinuity
  RealCurveDerivativeUP PartialFunctionUP MeasureDerivates ScalarIntervalDerivationContext
  StieltjesImageMeasures MeasureSubsetIntegral MeasureAlmostUP MeasureAlmostBasic
  LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_9_22]: complete Federer 2.9.22,
    pp. 167–168, extending 2.9.19, pp. 163–165, and
    2.9.20, pp. 165–166. Assume exactly the abstract normed
    continuous dual/bidual laws, the canonical reflexive embedding,
    Banach completeness and locally finite variation. There is no
    separability or global finite-variation premise. Actual strong
    norm derivatives and all scalar derivative identities share one
    conull set. For each fixed scalar functional and its actual
    induced pair, the two measure derivates have the printed
    alternatives almost everywhere; no uncountable intersection is
    claimed for those measure graphs. The norm integral bound includes
    a=b as a boundary extension. Absolute continuity uses the four
    actual integral/family/relative continuity conditions on a<b. *)
Theorem federer_2_9_22 (R : realType) (E D B : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> real_norm_metric_space hN) :
  is_complete_metric_space (real_norm_metric_space hN) ->
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : E,
    has_normed_curve_derivative N g x v /\
    has_real_curve_derivative (arc_length g) x (N v) /\
    punctured_real_limit (fun h => fine (signed_curve_variation g x (x+h))/h) (N v) /\
    forall alpha, has_real_curve_derivative (fun t => ed alpha (g t)) x (ed alpha v)] /\
  (forall a b : R, a<=b -> exists I : R, 0<=I /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (normed_curve_norm_derivative_integrand hN g) I%:E /\ (I%:E<=curve_variation g a b)%E) /\
  (forall (alpha : D) (psip psim : set R -> \bar R),
    is_induced_measure_pair (fun t => ed alpha (g t)) psip psim ->
    measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : E,
      has_normed_curve_derivative N g x v /\
      ((partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
          psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x (ed alpha v)%:E /\
        partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
          psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E) \/
       (partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
          psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x (-ed alpha v)%:E /\
        partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
          psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E))]) /\
  (forall a b : R, a<b ->
    (normed_curve_indefinite_derivative_integral hN g a b <->
      normed_curve_variation_integral_equality hN g a b) /\
    (normed_curve_variation_integral_equality hN g a b <->
      is_absolutely_continuous_metric_curve g a b) /\
    (is_absolutely_continuous_metric_curve g a b <->
      normed_curve_continuous_induced_measures hN ed g a b)).
Proof.
move=> hY ht hr hg.
have hNorm := @reflexive_bv_derivative_ae R E D B N hN ed DN hD eb BN hB tau g hY ht hr hg.
have hExists : measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v].
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ _ hNorm)=> x [v [hv _]]; by exists v.
split.
- exact (@reflexive_bv_variation_derivative_ae R E D B N hN ed DN hD eb BN hB tau g hY ht hr hg).
- split.
  + exact (@normed_bv_norm_derivative_interval_integral R E N hN g hg hExists).
  + split.
    * move=> alpha psip psim hp.
      exact (@normed_bv_scalar_induced_derivates_ae R E D N hN ed DN hD g alpha psip psim hg hExists hp).
    * move=> a b hab.
      exact (@normed_absolute_continuity_equivalences R E D N hN ed DN hD g a b hY hg hExists hab).
Qed.
