(** Federer (1969), 2.5.10, p. 101: integration on the finite-measure
    pieces. This supporting upper-integral identity follows directly from
    2.4.2, p. 81, and the cutoff in 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureStepFunctionUP MeasureStepIntegralIdentification MeasureZeroStepFunction MeasureIntegralComparison
  RestrictedStepIntegral RestrictedUpperFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_upper_step_integral_bound]: supporting
    upper-step comparison for Federer 2.5.10, p. 101.
    An upper function for a zero extension is nonnegative outside
    the piece, so deleting that contribution cannot increase its integral. *)
Lemma restricted_upper_step_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) a b :
  measure_measurable mu B ->
  is_measure_upper_function mu (partial_function_zero_extension (0 : extended_real_line R) B f) u ->
  is_measure_step_integral (measure_restrict mu B) u a -> is_measure_step_integral mu u b -> a <= b.
Proof.
move=> hB hu ha hb.
pose v := partial_function_zero_extension (0%R : real_line_metric R) B u.
have hv := @measure_step_zero_extension R X mu hm B u hB hu.1.
have hia := @measure_step_function_integral R X mu hm v a hv (proj1 (restricted_step_integral_iff mu B u a) ha).
have hib := @measure_step_function_integral R X mu hm u b hu.1 hb.
apply: (@measure_integral_monotone R X mu hm _ _ a b hia hib).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hu.2)=> x [r [z [hr [hz hzr]]]].
case: (pselect (B x))=> hx.
- exists r%:E,r%:E; split.
  + exists r; split=> //; apply/partial_function_zero_extension_graph; left; by split.
  + split; last exact: lexx; exists r; by split.
- have hz0 : z=0 := (proj1 (@partial_function_zero_extension_off X (extended_real_line R) 0 B f x z hx) hz).
  exists 0,r%:E; split.
  + exists 0%R; split=> //; apply/partial_function_zero_extension_graph; right; by split.
  + split; first by exists r; split.
    by rewrite -hz0.
Qed.

(** Source for [restricted_upper_integral_zero_extension]:
    supporting equality of the actual upper-integral bounds used in
    Federer 2.5.10, p. 101. It allows infinite bounds and
    nonmeasurable integrands, retaining exact partial domains. *)
Theorem restricted_upper_integral_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (f : partial_function X (extended_real_line R)) :
  measure_measurable mu B ->
  measure_upper_integral (measure_restrict mu B) f=
    measure_upper_integral mu (partial_function_zero_extension (0 : extended_real_line R) B f).
Proof.
move=> hB; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (measure_upper_integral_specification mu _).2=> b [u [hu hb]].
  have hlocal := @upper_function_for_restricted_measure R X mu hm B f u hB hu.
  have [a ha] := step_function_sum_defined hlocal.1.
  apply: (le_trans (@measure_upper_integral_bound R X (measure_restrict mu B) f u a hlocal ha)).
  exact: (@restricted_upper_step_integral_bound R X mu hm B f u a b hB hu ha hb).
- apply: (measure_upper_integral_specification (measure_restrict mu B) f).2=> b [u [hu hb]].
  have hglobal := @restricted_upper_zero_extension R X mu hm B f u hB hu.
  exact: (@measure_upper_integral_bound R X mu _ _ b hglobal (proj1 (restricted_step_integral_iff mu B u b) hb)).
Qed.
