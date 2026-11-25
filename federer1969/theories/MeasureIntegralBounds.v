(** Public upper and lower integrals of Federer (1969), 2.4.2, p. 81,
    derived only from the sealed bound specifications. Source context:
    MeasureIntegralUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureStepFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralBoundsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_integral]: public upper-integral
    value in Federer 2.4.2, p. 81, first defining display. *)
Definition measure_upper_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) := (@MeasureIntegralBounds.value R X mu f).1.

(** Source for [measure_lower_integral]: public lower-integral
    value in Federer 2.4.2, p. 81, first defining display. *)
Definition measure_lower_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) := (@MeasureIntegralBounds.value R X mu f).2.

(** Source for [measure_upper_integral_specification]: the upper
    value satisfies its defining infimum laws, Federer 2.4.2, p. 81. *)
Lemma measure_upper_integral_specification (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :
  is_measure_upper_integral mu f (measure_upper_integral mu f).
Proof. exact: (@MeasureIntegralBounds.laws R X mu f).1. Qed.

(** Source for [measure_lower_integral_specification]: the lower
    value satisfies its defining supremum laws, Federer 2.4.2, p. 81. *)
Lemma measure_lower_integral_specification (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :
  is_measure_lower_integral mu f (measure_lower_integral mu f).
Proof. exact: (@MeasureIntegralBounds.laws R X mu f).2. Qed.

(** Source for [measure_upper_integral_bound]: each upper
    function bounds the upper integral from above, directly from
    the definition in Federer 2.4.2, p. 81. *)
Lemma measure_upper_integral_bound (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) u a :
  is_measure_upper_function mu f u -> is_measure_step_integral mu u a -> measure_upper_integral mu f <= a.
Proof.
move=> hu ha; apply: (measure_upper_integral_specification mu f).1; exists u; by split.
Qed.

(** Source for [measure_lower_integral_bound]: each lower
    function bounds the lower integral from below, Federer 2.4.2, p. 81. *)
Lemma measure_lower_integral_bound (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) u a :
  is_measure_lower_function mu f u -> is_measure_step_integral mu u a -> a <= measure_lower_integral mu f.
Proof.
move=> hu ha; apply: (measure_lower_integral_specification mu f).1; exists u; by split.
Qed.
