(** Federer (1969), proof of 2.4.4(1), p. 82: a measurable function is
    integrable with value a if its upper integral is at most a and its lower
    integral is at least a. This is a supporting form of the squeeze
    argument using 2.4.3(7). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralBoundsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_squeeze]: supporting inference
    used in Federer 2.4.4(1),(4), pp. 82–83;
    the candidate value may be either infinity. *)
Lemma measure_integral_squeeze (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  is_measure_measurable_function mu f -> measure_upper_integral mu f <= a ->
  a <= measure_lower_integral mu f -> is_measure_integral mu f a.
Proof.
move=> hf hu hl; have h := @measure_lower_integral_le_upper R X mu hm f.
have eu : measure_upper_integral mu f = a.
  apply/eqP; rewrite eq_le hu /=; exact: le_trans hl h.
have el : measure_lower_integral mu f = a.
  apply/eqP; rewrite eq_le hl andbT; exact: le_trans h hu.
split=> //; split.
- rewrite -eu; exact: measure_upper_integral_specification.
- rewrite -el; exact: measure_lower_integral_specification.
Qed.
