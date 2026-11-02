(** Federer (1969), first assertion of 2.4.5, p. 83: a measurable set's
    characteristic function has integral equal to its measure. The
    characteristic map is supplied through its abstract laws, and real
    values are explicitly included in the extended real line. Source
    editions: MeasureAlmostSubsetBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionBasic MeasureUP CharacteristicFunctionUP
  MeasureStepCharacteristic MeasureStepIntegralIdentification MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_characteristic_integral]: direct first
    formula of Federer 2.4.5, p. 83; infinite measures
    are allowed and integrability is part of the conclusion. *)
Theorem measure_characteristic_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s -> measure_measurable mu A ->
  is_measure_integral mu (partial_real_function_embed (partial_function_total s)) (mu A).
Proof.
move=> hs hA; apply: (@measure_step_function_integral R X mu hm _ (mu A)).
- exact (@measure_characteristic_step_function R X mu hm A s hs hA).
- exact (@characteristic_step_assigned_sum R X mu hm A s hs).
Qed.
