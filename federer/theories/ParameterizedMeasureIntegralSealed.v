(** Federer (1969), 4.1.9, p. 363: the scalar
    integrals of the original time-dependent slice measures.
    This supporting parameterized integral permits the measure
    to vary with time. Its exact graph extends 2.6.2(4),
    p. 115, while retaining the partial-domain convention
    of 2.4.2, p. 81. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP ParameterizedMeasureIntegralUP ParameterizedMeasureIntegralConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ParameterizedMeasureIntegralSignature.
(** Source for [value]: abstract slice-integral function supporting
    Federer 4.1.9, p. 363. *)
Parameter value : forall (R : realType) (X : Type) (Y : choiceType),
  (X -> set Y -> \bar R) -> (X -> partial_function Y (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: exact integrability-domain and integral-
    value laws for the slice integrals supporting Federer 4.1.9, p. 363. *)
Parameter laws : forall (R : realType) (X : Type) (Y : choiceType)
  (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)),
  is_parameterized_measure_integral mu f (@value R X Y mu f).
End ParameterizedMeasureIntegralSignature.
Module ParameterizedMeasureIntegral : ParameterizedMeasureIntegralSignature.
(** Source for [value]: private choice of the proved inner-
    integral witness supporting the slice integrals supporting Federer 4.1.9, p. 363. *)
Definition value (R : realType) (X : Type) (Y : choiceType)
    (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :=
  projT1 (cid (@parameterized_measure_integral_exists R X Y mu f)).
(** Source for [laws]: the chosen witness satisfies the
    abstract specification for the slice integrals supporting Federer 4.1.9, p. 363. *)
Lemma laws (R : realType) (X : Type) (Y : choiceType)
    (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :
  is_parameterized_measure_integral mu f (@value R X Y mu f).
Proof. exact: projT2 (cid (@parameterized_measure_integral_exists R X Y mu f)). Qed.
End ParameterizedMeasureIntegral.
