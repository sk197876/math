(** Federer (1969), 2.4.10, p. 85: step-function restrictions used to split
    integral bounds. The defining countable-range and numerical-sum
    conditions come from 2.4.1, p. 80. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialZeroExtension
  CondensationKernel MeasureUP MeasurableZeroExtension MeasureStepFunctionUP MeasureZeroStepVariations NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_extension_countable_range]: supporting
    countability of the restricted step-function range in
    Federer 2.4.10, p. 85: only the value zero
    can be added to the original range. The elementary
    countable-adjunction lemma is reused from the project's 2.2.4. *)
Lemma zero_extension_countable_range (X : Type) (Y : choiceType) (zero : Y)
    (A : set X) (f : partial_function X Y) :
  countable (partial_function_range f) ->
  countable (partial_function_range (partial_function_zero_extension zero A f)).
Proof.
move=> hf; apply: sub_countable _ (countable_set_adjoin_point zero hf); apply: subset_card_le.
move=> y [x hx]; have [[ha hy]|[ha he]] := (partial_function_zero_extension_graph zero A f x y).1 hx.
- left; by exists x.
- right; by rewrite he.
Qed.

(** Source for [measure_step_zero_extension]: supporting closure
    of step functions under measurable restriction for Federer
    2.4.10, p. 85. Either original variation may
    be infinite, provided the assigned sum is defined. *)
Lemma measure_step_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u : partial_function X (real_line_metric R)) :
  measure_measurable mu A -> is_measure_step_function mu u ->
  is_measure_step_function mu (partial_function_zero_extension (0%R : real_line_metric R) A u).
Proof.
move=> hA hu; constructor.
- exact (@measurable_zero_extension R X [the topologicalType of real_line_metric R] mu hm 0%R A u hA (step_function_measurable hu)).
- exact: zero_extension_countable_range (step_function_countable_range hu).
- apply: (proj2 (numerical_sum_defined setT _)).
  have hside := (proj1 (numerical_sum_defined setT _)) (step_function_sum_defined hu).
  have [hp hn] := @zero_step_variation_bounds R X mu hm A u.
  apply/orP; move/orP: hside=> [hpos|hneg].
  + left; exact: le_lt_trans hp hpos.
  + right; exact: le_lt_trans hn hneg.
Qed.
