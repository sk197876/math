(** Federer (1969), 2.9.22, pp. 167–168: the complete Lipschitz argument in
    the separable reflexive case, through the actual norm derivative. The
    arbitrary-target closed- subspace reduction and the general locally BV
    argument are separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP MeasureAlmostUP MeasureAlmostBasic
  LebesgueScalarMeasure RealCurveDerivativeUP NormedCurveDerivativeUP NormedDerivativeDualEvaluation
  MeasureVectorIntegralUP MeasureRestriction PartialFunctionBasic
  ReflexiveLipschitzFieldUP ReflexiveLipschitzFieldSealed
  WeakDerivativeFieldVectorIntegral VectorPrimitiveLebesgueDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separable_reflexive_lipschitz_derivative_ae]:
    direct separable Lipschitz special case of Federer 2.9.22,
    pp. 167–168. A common conull set has actual strong
    norm derivatives bounded by L and the printed simultaneous
    characterisation against every continuous functional. The
    measurable weak field first gives actual interval vector
    integrals; the proved Lebesgue-point argument then gives
    the norm limit. Completeness is not separately invoked
    in this proof, since endpoint increments themselves supply
    the vector-integral witnesses. The nonseparable and locally
    BV reductions are not claimed by this theorem. *)
Theorem separable_reflexive_lipschitz_derivative_ae (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R)
    (C : set (real_norm_metric_space hN)) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  countable C -> dense C -> 0<=L ->
  (forall t u, N (g t-g u)<=L * `|t-u|) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists w : E, has_normed_curve_derivative N g x w /\ N w<=L /\
      forall alpha, has_real_curve_derivative (fun t => ed alpha (g t)) x (ed alpha w)].
Proof.
move=> ht hr hCc hCd hL hg.
pose v := @ReflexiveLipschitzField.value R E D B N hN ed DN hD eb BN hB tau g L C
  ht hr hCc hCd hL hg.
have hv := @ReflexiveLipschitzField.laws R E D B N hN ed DN hD eb BN hB tau g L C
  ht hr hCc hCd hL hg.
have hprimitive a b : a<b -> is_measure_vector_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (partial_function_total (v : real_line_metric R -> real_norm_metric_space hN)) (g b-g a).
  exact (@weak_derivative_field_vector_integral R E D N hN ed DN hD g v L a b C
    hCc hCd hL hg hv).
have hAE := @bounded_vector_primitive_derivative_ae R E N hN C g v L hCc hCd
  (bounded_weak_field_measurable hv) (bounded_weak_field_bound hv) hprimitive.
apply: (@measure_almost_everywhere_mono R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hAE)=> x hx.
exists (v x); split=> //; split; first exact: bounded_weak_field_bound hv x.
exact (@normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x (v x) hx).
Qed.
