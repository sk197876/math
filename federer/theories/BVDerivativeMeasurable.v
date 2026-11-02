(** Federer (1969), 2.9.22, pp. 167–168: actual norm derivatives belong to
    the measurable, essentially separable class needed by the vector
    integral in the extension of 2.9.20(1), p. 165. Use the already proved
    derivative existence and the positive reciprocal quotients of the Borel
    BV curve. The project's full partial-domain measurable-limit theorem
    retains the exact derivative graph; no total representative is selected
    here. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP CurveArcLength
  NormedCurveDerivativeUP NormedPuncturedSequenceLimit BVCurveMeasurable
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP
  MeasurableNormedFunctionUP MeasurableNormedLimit
  MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_bv_derivative_measurable]: supporting actual
    norm derivative measurability for Federer 2.9.22, pp. 167–168,
    extending 2.9.20(1), p. 165. The auxiliary quotients are
    measurable and essentially separable. At each actual derivative
    point they converge in norm to that exact partial graph value.
    The existing full partial-limit theorem proves membership in
    A(L^1,Y). Reflexivity supplies the explicit existence premise in
    the theorem above; no converse from sequence limits is used. *)
Theorem normed_bv_derivative_measurable (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  @is_measurable_normed_function R (real_line_metric R) E N hN (@lebesgue_scalar_measure R)
    (normed_curve_derivative hN g).
Proof.
move=> hY hg he.
pose q (n : nat) (x : real_line_metric R) : real_norm_metric_space hN :=
  ((n.+1)%:R : R)^-1^-1 *: (g (x+((n.+1)%:R : R)^-1)-g x).
have hq n := @complete_normed_bv_difference_quotient_measurable R E N hN g
  (((n.+1)%:R : R)^-1) hY hg.
have hlim : measure_almost_everywhere (@lebesgue_scalar_measure R)
    (partial_function_limit_locus (fun n => partial_function_total (q n))
      (normed_curve_derivative hN g)).
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ _ he)=> x [v hv].
  exists (fun n => q n x),v; split; first by move=> n.
  split; first exact hv.
  exact (@punctured_norm_limit_reciprocal_sequence R E N hN
    (fun h => h^-1 *: (g (x+h)-g x)) v hv).
exact (@measurable_normed_almost_limit R (real_line_metric R) E N hN
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  (fun n => partial_function_total (q n)) (normed_curve_derivative hN g) hq hlim).
Qed.
