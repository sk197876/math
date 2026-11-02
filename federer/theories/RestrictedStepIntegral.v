(** Federer (1969), 2.5.10, p. 101: supporting integral identity for the
    restrictions used to construct local densities. The step-integral
    definition is 2.4.1, p. 80, and the cutoff convention is 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureRestriction MeasureStepFunctionUP MeasureZeroStepVariations MeasureZeroStepFunction
  RestrictedFunctionMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_step_integral_iff]: supporting identity
    between integration for the restricted measure and the zero extension
    in Federer 2.5.10, p. 101. The zero fibre contributes zero
    even when it has infinite measure. No measurability is needed
    for this equality of the assigned numerical sums. *)
Lemma restricted_step_integral_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (B : set X) (u : partial_function X (real_line_metric R)) z :
  is_measure_step_integral (measure_restrict mu B) u z <->
  is_measure_step_integral mu (partial_function_zero_extension (0%R : real_line_metric R) B u) z.
Proof.
rewrite /is_measure_step_integral.
have he : (fun y : R => y%:E * measure_restrict mu B (partial_function_preimage u [set y]))=
    (fun y : R => y%:E * mu (partial_function_preimage
      (partial_function_zero_extension (0%R : real_line_metric R) B u) [set y])).
  apply: funext=> y; case: (eqVneq y 0%R)=> hy.
  - by rewrite hy !mul0e.
  - have hy' : y <> 0%R by move=> h; move: hy; rewrite h eqxx.
    by rewrite (@zero_extension_nonzero_fibre X (real_line_metric R) 0%R y B u hy').
by rewrite he.
Qed.

(** Source for [restricted_step_zero_extension]: supporting step
    function transfer for Federer 2.5.10, p. 101, derived from
    the definitions in 2.4.1 and 2.4.10, pp. 80, 85. *)
Lemma restricted_step_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (u : partial_function X (real_line_metric R)) :
  measure_measurable mu B -> is_measure_step_function (measure_restrict mu B) u ->
  is_measure_step_function mu (partial_function_zero_extension (0%R : real_line_metric R) B u).
Proof.
move=> hB hu; constructor.
- exact: restricted_measurable_zero_extension hB (step_function_measurable hu).
- exact: zero_extension_countable_range (step_function_countable_range hu).
- have [z hz] := step_function_sum_defined hu; exists z; exact: (proj1 (restricted_step_integral_iff mu B u z) hz).
Qed.

(** Source for [step_function_for_restricted_measure]: supporting
    converse step-function transfer for Federer 2.5.10, p. 101.
    Restricting to a measurable set preserves definedness of the
    signed numerical sum, including infinite values. *)
Lemma step_function_for_restricted_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (u : partial_function X (real_line_metric R)) :
  measure_measurable mu B -> is_measure_step_function mu u ->
  is_measure_step_function (measure_restrict mu B) u.
Proof.
move=> hB hu; constructor.
- exact: (@measurable_function_for_restricted_measure R X [the topologicalType of real_line_metric R] mu hm B u (step_function_measurable hu)).
- exact: step_function_countable_range hu.
- have [z hz] := step_function_sum_defined (@measure_step_zero_extension R X mu hm B u hB hu).
  exists z; exact: (proj2 (restricted_step_integral_iff mu B u z) hz).
Qed.
