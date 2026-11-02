(** Supporting first step of the contradiction in Federer (1969), 2.6.3(2),
    p. 118. Both actual iterated integrals have already been proved zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import MeasureIntegralUP MeasureIntegralUniqueness ProductMeasure ProductFunctionFubini
  LebesgueScalarMeasure LebesgueProductIntegrands RationalIteratedIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [rational_integrable_product_value_zero]: hypothetical
    integrability in Federer 2.6.3(2), p. 118, forces finite value zero by
    the proved iterated integrals and 2.6.2(4), p. 115 This is a conditional
    step, not an assertion of integrability. *)
Lemma rational_integrable_product_value_zero (R : realType) (z : \bar R) :
  is_measure_integral
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (@rational_fubini_integrand R) z -> z=0.
Proof.
move=> hi; have hc := lebesgue_product_function_countably_measurable hi.1.
have hf := @product_function_fubini R R R _ _ (lebesgue_scalar_is_measure R)
  (lebesgue_scalar_is_measure R) _ z hi hc.
exact: measure_integral_unique hf.2 (@rational_fubini_iterated_integrals_zero R).1.
Qed.
