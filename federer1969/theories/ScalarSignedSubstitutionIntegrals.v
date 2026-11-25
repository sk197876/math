(**  Federer (1969), 3.2.6, pp. 245–246:
    summability and subtraction of the two sign pieces
    prove the second substitution identity as a common
    finite actual integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground LocallyAbsolutelyContinuousCurve ScalarAbsoluteContinuousArea
  ScalarSignedSourceSplitting ScalarSignedMultiplicityAlmost ScalarSignedPieceIntegrals
  PartialFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralDifference MeasureIntegralAlmostEquality
  LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(**  Source for [scalar_signed_substitution_finite_integrals]:
    the final equality in Federer 3.2.6, pp. 245–246.
    The sole weight hypothesis is the erratum-corrected
    Lebesgue summability of g times full multiplicity.
    Both signed integrals exist and have the same finite value. *)
Theorem scalar_signed_substitution_finite_integrals (R:realType) (f g:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> a<b ->
  is_measure_summable (@lebesgue_scalar_measure R) (scalar_curve_area_target_integrand f `[a,b] g) ->
  exists z:R,
    is_measure_integral (@lebesgue_scalar_measure R) (scalar_signed_substitution_source f g a b) z%:E /\
    is_measure_integral (@lebesgue_scalar_measure R) (scalar_oriented_interval_integrand g (f a) (f b)) z%:E.
Proof.
move=>hAC hab hSum; have hm:=lebesgue_scalar_is_measure R.
have [p [q [hU [hV [hP hN]]]]]:=scalar_signed_piece_finite_integrals hAC hab hSum.
exists (p-q)%R; split.
- exact (measure_integral_almost_equal hm
    (measure_integral_finite_difference hm hU hV) (@scalar_signed_source_sign_split R f g a b hAC)).
- exact (measure_integral_almost_equal hm
    (measure_integral_finite_difference hm hP hN) (@scalar_signed_target_sign_split R f g a b hAC hab)).
Qed.
