(** Federer (1969), 2.9.20, p. 166: split the derivative integral at
    interior points when taking the endpoint limit. This supporting finite
    identity follows the interval-additivity convention of 2.4.10, p. 85.
    Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureSubsetIntegral MeasureIntegralUniqueness LebesgueScalarMeasure RealSegmentIntegralDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_lebesgue_interval_integral_split]: supporting finite
    integral splitting for Federer 2.9.20, p. 166 Three existing finite
    integrals over [a,b], [a,u] and [u,b] satisfy the usual additive
    identity, regardless of integrand values at u. *)
Lemma finite_lebesgue_interval_integral_split (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (a u b A B C : R) : a<=u -> u<=b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b] f A%:E ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,u] f B%:E ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,b] f C%:E -> A=B+C.
Proof.
move=> hau hub hA hB hC.
have hD := @lebesgue_segment_integral_finite_difference R f a u b B A hau hub hB hA.
have he := measure_integral_unique hD hC.
have hr : A-B=C by case: he.
lra.
Qed.
