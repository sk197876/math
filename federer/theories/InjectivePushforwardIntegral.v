(** Federer (1969), 3.2.6, p. 245: integral
    transport through the bijective scalar coordinate map
    uses 2.4.18 without a finite total-mass assumption.
    Injectivity gives the converse measurability implication. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasureIntegralUP PushforwardIntegral PushforwardMeasurabilityTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [injective_pushforward_integral_iff]: supporting
    coordinate transport of the scalar curve formula in
    Federer 3.2.6, p. 245. Both integral definedness
    and values are retained for the original partial graph. *)
Theorem injective_pushforward_integral_iff (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (u:X->Y)
    (f:partial_function Y (extended_real_line R)):
  injective u -> forall a,
  is_measure_integral mu (partial_function_precompose u f) a <->
  is_measure_integral (measure_pushforward u mu) f a.
Proof.
move=>hInj a; split=>hi.
- exact ((measure_pushforward_integral_iff hm hi.1 a).1 hi).
- have hMeas:=measurable_function_pushforward_precompose hInj hi.1.
  exact ((measure_pushforward_integral_iff hm hMeas a).2 hi).
Qed.
