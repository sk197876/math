(** Federer (1969), 2.4.18, pp. 90–91, used in
    4.1.8, p. 361: integration through the original
    coordinate bijection. Derive both directions from the
    original image-measure theorem, including completed
    measurability and every signed integral value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasurableFunctionUP MeasureIntegralUP
  MeasureBijectionUP PushforwardMeasurableFunctions PushforwardMeasurabilityTransfer PushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section MeasureBijectionIntegralTransport.
Variable R:realType.
Variables X Y:choiceType.
Variables (mu:set X->\bar R) (nu:set Y->\bar R).
Hypothesis hm:is_measure mu.
Variables (u:X->Y) (ui:Y->X).
Hypothesis hBij:is_measure_bijection mu nu u ui.

(** Source for [measure_bijection_measurable_iff]: the original
    coordinate bijection preserves completed measurability in
    both directions, supporting Federer 4.1.8, p. 361,
    by 2.4.18(1), p. 90. *)
Theorem measure_bijection_measurable_iff (Z:topologicalType) (f:partial_function Y Z):
  is_measure_measurable_function mu (partial_function_precompose u f) <->
    is_measure_measurable_function nu f.
Proof.
split.
- move=>hF;have h:=pushforward_function_measurable_from_composition hF.
  by rewrite (measure_bijection_pushforward hBij) in h.
- move=>hF.
  rewrite -(measure_bijection_pushforward hBij) in hF.
  exact:(measurable_function_pushforward_precompose (can_inj (measure_bijection_cancel hBij)) hF).
Qed.

(** Source for [measure_bijection_integral_iff]: the original
    coordinate bijection preserves the full original integral,
    supporting Federer 4.1.8, p. 361, by 2.4.18(1),
    p. 90. Undefined signed differences receive no value. *)
Theorem measure_bijection_integral_iff
    (f:partial_function Y (extended_real_line R)) a:
  is_measure_integral mu (partial_function_precompose u f) a <->
    is_measure_integral nu f a.
Proof.
split=>hI.
- have h:=(@measure_pushforward_integral_iff R X Y mu hm u f hI.1 a).1 hI.
  by rewrite (measure_bijection_pushforward hBij) in h.
- have hF:=(measure_bijection_measurable_iff f).2 hI.1.
  apply:(@measure_pushforward_integral_iff R X Y mu hm u f hF a).2.
  by rewrite (measure_bijection_pushforward hBij).
Qed.
End MeasureBijectionIntegralTransport.
