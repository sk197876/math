(** Federer (1969), 3.2.6, pp. 245–246: bounded
    absolutely continuous curves give finite regular speed
    measures. In that situation 2.4.18 applies in both
    directions, including integral definedness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasurePushforward RegularMeasureUP MeasureIntegralUP PushforwardIntegral PushforwardMeasurableFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_regular_pushforward_integral_iff]:
    supporting finite-measure version of 2.4.18 in
    Federer 3.2.6, p. 245. Finite regularity
    supplies composition measurability from a target integral,
    so no independent measurability premise is imposed. *)
Theorem finite_regular_pushforward_integral_iff (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_regular_measure mu)
    (u:X->Y) (f:partial_function Y (extended_real_line R)):
  mu setT< +oo -> forall a,
  is_measure_integral mu (partial_function_precompose u f) a <->
  is_measure_integral (measure_pushforward u mu) f a.
Proof.
move=>hFin a; split=>hi.
- exact ((measure_pushforward_integral_iff hm hi.1 a).1 hi).
- have hMeas:=@regular_pushforward_measurable_composition R X Y (extended_real_line R)
    mu hm hr u f hFin hi.1.
  exact ((measure_pushforward_integral_iff hm hMeas a).2 hi).
Qed.
