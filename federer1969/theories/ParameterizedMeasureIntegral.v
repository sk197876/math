(** Federer (1969), 4.1.9, p. 363: the scalar
    integrals of the original time-dependent slice measures.
    This supporting parameterized integral permits the measure
    to vary with time. Its exact graph extends 2.6.2(4),
    p. 115, while retaining the partial-domain convention
    of 2.4.2, p. 81. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP ParameterizedMeasureIntegralUP ParameterizedMeasureIntegralSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [parameterized_measure_integral]: public inner-integral
    function supporting Federer 4.1.9, p. 363, with
    no values outside the actual integrability domain. *)
Definition parameterized_measure_integral (R : realType) (X : Type) (Y : choiceType)
    (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :=
  @ParameterizedMeasureIntegral.value R X Y mu f.

(** Source for [parameterized_measure_integral_specification]: exposed
    graph laws for the inner integral supporting Federer 4.1.9, p. 363. *)
Lemma parameterized_measure_integral_specification (R : realType) (X : Type) (Y : choiceType)
    (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :
  is_parameterized_measure_integral mu f (parameterized_measure_integral mu f).
Proof. exact: ParameterizedMeasureIntegral.laws. Qed.

(** Source for [parameterized_measure_integral_domain]: exact domain
    of the inner-integral function supporting Federer 4.1.9,
    p. 363: precisely the parameters with an integrable section. *)
Lemma parameterized_measure_integral_domain (R : realType) (X : Type) (Y : choiceType)
    (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) x :
  partial_function_domain (parameterized_measure_integral mu f) x <-> is_measure_integrable (mu x) (f x).
Proof.
split=> [[a ha]|[a ha]]; exists a.
- exact: (parameterized_measure_integral_specification mu f x a).1 ha.
- exact: (parameterized_measure_integral_specification mu f x a).2 ha.
Qed.
