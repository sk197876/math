(** Federer (1969), 2.5.10, p. 101: upper-function transfer needed to
    compare the local integral with the original one. The definitions are
    2.4.2, p. 81, and 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  RestrictedAlmostEverywhere RestrictedStepIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_upper_zero_extension]: supporting
    transfer of local upper functions in Federer 2.5.10, p. 101.
    Zero outside the piece satisfies the extended-real upper inequality. *)
Lemma restricted_upper_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) :
  measure_measurable mu B -> is_measure_upper_function (measure_restrict mu B) f u ->
  is_measure_upper_function mu (partial_function_zero_extension (0 : extended_real_line R) B f)
    (partial_function_zero_extension (0%R : real_line_metric R) B u).
Proof.
move=> hB hu; split; first exact: (@restricted_step_zero_extension R X mu hm B u hB hu.1).
have hh := (proj1 (restricted_almost_everywhere_iff mu B _)) hu.2.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hh)=> x hx.
case: (pselect (B x))=> hb.
- have [r [z [hr [hz hzr]]]] := hx hb; exists r,z; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split=> //; apply/partial_function_zero_extension_graph; left; by split.
- exists 0%R,0; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split=> //; apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [upper_function_for_restricted_measure]: supporting
    converse upper-function transfer in Federer 2.5.10, p. 101.
    Its step integral for the restriction can differ from the original
    step integral; the following bound handles that distinction. *)
Lemma upper_function_for_restricted_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) :
  measure_measurable mu B ->
  is_measure_upper_function mu (partial_function_zero_extension (0 : extended_real_line R) B f) u ->
  is_measure_upper_function (measure_restrict mu B) f u.
Proof.
move=> hB hu; split; first exact: (@step_function_for_restricted_measure R X mu hm B u hB hu.1).
apply: (proj2 (restricted_almost_everywhere_iff mu B _)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hu.2)=> x [r [z [hr [hz hzr]]]] hb.
exists r,z; split=> //; split=> //.
exact: (proj1 (@partial_function_zero_extension_on X (extended_real_line R) 0 B f x z hb) hz).
Qed.
