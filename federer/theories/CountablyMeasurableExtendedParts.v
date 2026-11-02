(** Federer (1969), 2.6.2(4), p. 117: the positive/negative-part reduction
    preserves the countably measurable nonzero-locus condition of 2.3.4, p.
    76. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasurableFunctionUP MeasurableExtendedParts MeasureUpperIntegralPositivePart PartialFunctionIntegralParts
  CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableSubsets CountablyMeasurableNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_extended_parts]: supporting
    positive/negative-part support containment in Federer 2.6.2(4),
    p. 117, using the definition in 2.3.4, p. 76. *)
Lemma countably_measurable_extended_parts (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  is_countably_measure_measurable_function mu (0 : extended_real_line R) f ->
  is_countably_measure_measurable_function mu (0 : extended_real_line R) (partial_extended_function_positive_part f) /\
  is_countably_measure_measurable_function mu (0 : extended_real_line R) (partial_extended_function_negative_part f).
Proof.
move=> hf.
have hp := @measurable_extended_positive_part R X mu hm f (countably_measurable_function_measurable hf).
have hn := @measurable_extended_negative_part R X mu hm f (countably_measurable_function_measurable hf).
split.
- constructor; first exact hp.
  refine (@measurable_subset_countably_measurable R X mu hm _ (partial_function_nonzero_locus 0 f)
    (@measurable_function_nonzero_locus R X (extended_real_line R) mu hm 0 _ (@extended_real_zero_closed R) hp)
    _ (countably_measurable_function_locus hf)).
  move=> x [y [[z [hz ezy]] hy0]]; exists z; split=> // ez.
  apply: hy0; rewrite -ezy ez /extended_positive_part; exact: maxxx.
- constructor; first exact hn.
  refine (@measurable_subset_countably_measurable R X mu hm _ (partial_function_nonzero_locus 0 f)
    (@measurable_function_nonzero_locus R X (extended_real_line R) mu hm 0 _ (@extended_real_zero_closed R) hn)
    _ (countably_measurable_function_locus hf)).
  move=> x [y [[z [hz ezy]] hy0]]; exists z; split=> // ez.
  apply: hy0; rewrite -ezy ez /extended_negative_part /extended_positive_part oppe0; exact: maxxx.
Qed.
