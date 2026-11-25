(** Private existence proof for the bounded measurable field v of Federer
    (1969), 2.9.22, p. 167. The public specification is
    ReflexiveLipschitzFieldUP.v. Representatives are chosen only after the
    common conull-set existence theorem; scalar measurability follows from
    actual difference quotients, and norm measurability from countable
    norming tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  NormMetricScaleContinuity RealFunctionalNormUP ContinuousDualUP ContinuousDualNorm
  ContinuousBidualUP PartialFunctionBasic MeasurableFunctionUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure
  RealCurveDerivativeUP LipschitzDualScalarisation ReflexiveLipschitzWeakDerivative
  SeparableReflexiveDual ContinuousDerivativeMeasurable MeasurableDualEvaluationCriterion
  ReflexiveLipschitzFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reflexive_lipschitz_field_exists]: supporting
    existence of the bounded measurable v in Federer 2.9.22,
    p. 167, before the integral display. Separability of Y
    yields dual separability by the proved reflexivity argument.
    No separable-dual premise or norm differentiability premise
    is added. The arbitrary representative off the common
    conull set is chosen bounded, and hidden by sealing. *)
Theorem reflexive_lipschitz_field_exists (R : realType)
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
  exists v : R -> E, is_bounded_weak_derivative_field hN ed
    (@lebesgue_scalar_measure R) g v L.
Proof.
move=> ht hr hCc hCd hL hg.
have [F [hFc hFd]] := @separable_reflexive_dual R E D B N hN ed DN hD eb BN hB
  tau C ht hr hCc hCd.
have hAE := @reflexive_lipschitz_weak_derivative_ae R E D B N hN ed DN hD eb BN hB
  tau g L F ht hr hFc hFd hL hg.
pose P (x : R) := exists v : E, N v<=L /\ is_weak_normed_curve_derivative ed g x v.
have hone x : exists v : E, N v<=L /\ (P x -> is_weak_normed_curve_derivative ed g x v).
  case: (pselect (P x))=> [[v [hv hd]]|hn].
    by exists v; split.
  exists 0; split; first by rewrite (real_seminorm_zero hN.1).
  by move=> hx; exact: False_ind _ (hn hx).
have [v hv] := choice hone.
have hweak : measure_almost_everywhere (@lebesgue_scalar_measure R)
    (fun x => is_weak_normed_curve_derivative ed g x (v x)).
  apply: (@measure_almost_everywhere_mono R (real_line_metric R)
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hAE).
  by move=> x hx; exact: (hv x).2 hx.
have hscalar a : is_measure_measurable_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun x => (ed a (v x) : real_line_metric R))).
  have hDa := real_functional_norm_nonnegative (continuous_dual_norm_laws hD a).
  have hLip := @normed_lipschitz_scalarisation R E D N hN ed DN hD g L hg a.
  have hcont := @metric_fixed_lipschitz_continuous R
    [the metricType R of real_line_metric R] [the metricType R of real_line_metric R]
    (fun t => ed a (g t)) (DN a * L) (mulr_ge0 hDa hL) hLip.
  have hd : measure_almost_everywhere (@lebesgue_scalar_measure R)
      [set x | has_real_curve_derivative (fun t => ed a (g t)) x (ed a (v x))].
    apply: (@measure_almost_everywhere_mono R (real_line_metric R)
      (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hweak).
    by move=> x hx; exact: hx a.
  exact (@continuous_scalar_derivative_representative_measurable R
    (@lebesgue_scalar_measure R) (fun t => ed a (g t)) (fun t => ed a (v t))
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) hcont hd).
exists v; constructor.
- move=> x; exact: (hv x).1.
- exact hweak.
- exact ((@measurable_from_dual_evaluations R (real_line_metric R) E D N hN
    ed DN hD C (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) v hCc hCd).2 hscalar).
Qed.
