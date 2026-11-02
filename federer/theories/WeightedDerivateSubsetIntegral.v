(** Federer (1969), 2.9.21, p. 166: combine 2.9.7 with the change-of-density
    formula 2.4.10. All integrals and density products retain their actual
    partial domains and signed definedness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialDensityProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasurableFunctionUP MeasurableZeroExtension MeasureIntegralUP MeasureSubsetIntegral
  MeasureDerivationContext MeasureDerivates DerivationMeasurable DerivationLevelSeparation
  DerivateDensitySpecification AbsoluteContinuousPart MeasureChangeOfDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_derivate_subset_integral]: direct supporting
    weighted use of 2.9.7 in Federer 2.9.21, p. 166. An actual integral of
    f_A with respect to the continuous part equals the integral of f_A times
    the actual derivate with respect to the reference measure. Undefined
    derivative values are not filled in. *)
Lemma weighted_derivate_subset_integral (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X)
    (f : partial_function X (extended_real_line R)) (z : \bar R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_measurable phi A -> is_measure_measurable_function phi f ->
  is_measure_subset_integral (measure_continuous_part psi phi) A f z ->
  is_measure_integral phi (partial_density_product
    (partial_function_zero_extension (0 : extended_real_line R) A f)
    (measure_derivate psi phi V)) z.
Proof.
move=> hc hp hA hf hI.
have hm := derivation_measure_law (derivation_context_measure hc).
have hD := @federer_2_9_6 R X phi psi V hc hp.
have hpos : measure_almost_everywhere phi
    (partial_extended_nonnegative_locus (measure_derivate psi phi V)).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measurable_function_domain hD))=> x [y hy].
  exists y; split=> //; exact: measure_derivate_value_nonnegative hm (derivation_measure_law hp) hy.
have hCut := @measurable_zero_extension R X (extended_real_line R) phi hm 0 A f hA hf.
exact: (@measure_density_integral_iff R X phi (measure_continuous_part psi phi) hm _ _
  (@derivate_continuous_part_density_specification R X phi psi V hc hp) hD hpos hCut z).1 hI.
Qed.
