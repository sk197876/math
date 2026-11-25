(** Federer (1969), 4.1.9, p. 363: the scalar
    integrals of the original time-dependent slice measures.
    This supporting parameterized integral permits the measure
    to vary with time. Its exact graph extends 2.6.2(4),
    p. 115, while retaining the partial-domain convention
    of 2.4.2, p. 81. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP
  MeasureIntegralUniqueness ParameterizedMeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [parameterized_measure_integral_exists]: integral
    uniqueness gives the partial function of the original
    slice integrals, supporting Federer 4.1.9, p. 363.
    This construction serves only as an existence proof. *)
Theorem parameterized_measure_integral_exists (R : realType) (X : Type) (Y : choiceType)
    (mu : X -> set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :
  exists g, is_parameterized_measure_integral mu f g.
Proof.
have hs : forall x a b, is_measure_integral (mu x) (f x) a -> is_measure_integral (mu x) (f x) b -> a = b.
  move=> x a b; exact: measure_integral_unique.
exists (@Build_partial_function X (extended_real_line R)
  (fun x a => is_measure_integral (mu x) (f x) a) hs).
by move=> x a.
Qed.
