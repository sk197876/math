(** Federer (1969), 2.9.25, p. 169, full proposition: the finite joint
    integral and the printed iterated prefix formula imply absolute
    continuity of g and g'(t) equal to the section integral for Lebesgue
    almost all t in I. The proof follows the cited 2.6.2, 2.9.8 and 2.9.20.
    No relevant correction occurs in the local Federer erratum. A total real
    u on the product is restricted to S times I in the joint integral; its
    values outside I are irrelevant. The curve is also constrained only on
    I. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialZeroExtension PartialProductSections
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  ProductMeasure ParameterizedIntegral ParameterIntegralPrimitive ProductSubsetInterchange
  SummablePrimitiveAbsoluteContinuity SummablePrimitiveDifferentiation
  SummableRealFunctionUP RealCurveDerivativeUP RealAbsoluteContinuityUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_parameter_integral_differentiation]: supporting
    partial-integrand generalisation of Federer 2.9.25, p. 169 The finite
    actual product integral provides conull inner-integrability domains. The
    conclusion retains the original section integral rather than a selected
    representative or an undefined default value. *)
Theorem partial_parameter_integral_differentiation (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (hp : is_measure phi)
    (f : partial_function (X*real_line_metric R) (extended_real_line R))
    (g : R -> R) (a b J : R) : a<b ->
  is_measure_subset_integral (product_measure hp (lebesgue_scalar_is_measure R))
    (setT `*` `[a,b]) f J%:E ->
  (forall t : R, a<=t -> t<=b -> is_measure_integral phi
    (parameterized_integral (@lebesgue_scalar_measure R) (fun x =>
      partial_function_zero_extension (0 : extended_real_line R) `[a,t]
        (partial_product_vertical_section f x))) (g t)%:E) ->
  is_absolutely_continuous_real_curve g a b /\
  measure_almost_everywhere_on (@lebesgue_scalar_measure R) `[a,b]
    [set t | exists v : R, has_real_curve_derivative g t v /\
      is_measure_integral phi (partial_product_horizontal_section f t) v%:E].
Proof.
move=> hab hJ hG.
pose F := partial_function_zero_extension (0 : extended_real_line R) (setT `*` `[a,b]) f.
pose h := parameterized_integral phi (partial_product_horizontal_section F).
have [hsum hF] := @parameter_integral_prefix_primitive R X phi hp f g a b J hJ hG.
split; first exact: summable_primitive_absolute_continuity hsum hF.
have hAE := @summable_primitive_derivative_almost_everywhere R h g a b hsum hF.
apply/(measure_almost_everywhere_on_implication (@lebesgue_scalar_measure R) `[a,b] _).
have hAE' := (measure_almost_everywhere_on_implication (@lebesgue_scalar_measure R) `[a,b] _).1 hAE.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hAE')=> t ht hIt.
have [v [hd hv]] := ht hIt.
exists v; split=> //.
have hv' := (@parameterized_integral_subset_horizontal_graph R X (real_line_metric R)
  phi hp `[a,b] f t v%:E).1 hv.
have hv'' := (partial_function_zero_extension_on _ _ _ hIt).1 hv'.
exact: (parameterized_integral_specification phi (partial_product_horizontal_section f) t v%:E).1 hv''.
Qed.

(** Source for [federer_2_9_25]: direct complete proposition of Federer
    2.9.25, p. 169 A real joint function with a finite actual integral gives
    an absolutely continuous iterated primitive, whose actual derivative
    equals its section integral almost everywhere on the closed interval.
    Neither a sigma-finite first measure nor bounds on u nor hypotheses on g
    outside the interval are added. The two endpoint exceptions are null. *)
Theorem federer_2_9_25 (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (hp : is_measure phi)
    (u : X*real_line_metric R -> R) (g : R -> R) (a b J : R) : a<b ->
  is_measure_subset_integral (product_measure hp (lebesgue_scalar_is_measure R))
    (setT `*` `[a,b]) (real_total_integrand u) J%:E ->
  (forall t : R, a<=t -> t<=b -> is_measure_integral phi
    (parameterized_integral (@lebesgue_scalar_measure R) (fun x =>
      partial_function_zero_extension (0 : extended_real_line R) `[a,t]
        (partial_product_vertical_section (real_total_integrand u) x))) (g t)%:E) ->
  is_absolutely_continuous_real_curve g a b /\
  measure_almost_everywhere_on (@lebesgue_scalar_measure R) `[a,b]
    [set t | exists v : R, has_real_curve_derivative g t v /\
      is_measure_integral phi (partial_product_horizontal_section (real_total_integrand u) t) v%:E].
Proof. exact: partial_parameter_integral_differentiation. Qed.
