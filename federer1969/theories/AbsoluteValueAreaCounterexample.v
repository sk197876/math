(** Federer (1969), 3.2.7, p. 246, final
    counterexample to removing source integrability from
    3.2.3(2). The map is |x| and the weight is x;
    the actual target integral is zero and the actual
    source integral is undefined. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialDensityProduct
  RealCurveDerivativeIntegrands SummableRealFunctionUP PartialFibreNumericalSum ScalarAbsoluteValueCurve
  ScalarIdentityNotIntegrable AbsoluteValueSignedFibres MeasureUP MeasureIntegralUP MeasureIntegralAlmostEquality
  LebesgueScalarMeasure LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_7_4]: the complete final
    counterexample of Federer 3.2.7, p. 246,
    written on the scalar carrier of R^1. The
    actual one-dimensional Jacobian is the speed,
    by the proved scalar/Euclidean adapter of 3.2.6. *)
Theorem federer_3_2_7_4 (R:realType):
  is_metric_lipschitz setT (fun x:real_line_metric R=>(`|x| : real_line_metric R)) /\
  ~is_measure_integrable (@lebesgue_scalar_measure R)
    (partial_density_product (real_total_integrand (fun x:R=>x))
      (real_curve_absolute_derivative_integrand (fun x:R=>`|x|))) /\
  is_measure_integral (@lebesgue_scalar_measure R)
    (@partial_fibre_numerical_sum R [the choiceType of real_line_metric R] R
      (fun x:R=>`|x|) (real_total_integrand (fun x:R=>x))) 0%E.
Proof.
split.
- exists 1%R; split; first exact:ltr01.
  exact:scalar_absolute_value_nonexpanding.
split; last exact:absolute_value_signed_fibre_integral_zero.
move=>[a ha]; apply:(@scalar_identity_not_integrable R); exists a.
exact (measure_integral_almost_equal (lebesgue_scalar_is_measure R) ha
  (@absolute_value_weighted_source_identity_almost R)).
Qed.
