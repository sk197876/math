(** Federer (1969), 2.5.10, p. 101: recovering local measurability from a
    zero extension. The cutoff convention is 2.4.10, p. 85; almost equality
    is 2.3.1–2.3.2, pp. 72–73. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialZeroExtension MeasureUP MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableAlmostModification
  RestrictedAlmostEverywhere RestrictedFunctionMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [zero_extension_measurable_for_restriction]:
    supporting converse measurability step in Federer 2.5.10,
    p. 101. This direction needs no measurability of the piece. *)
Lemma zero_extension_measurable_for_restriction (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y)
    (B : set X) (f : partial_function X Y) :
  is_measure_measurable_function mu (partial_function_zero_extension zero B f) ->
  is_measure_measurable_function (measure_restrict mu B) f.
Proof.
move=> hg.
have hgn := @measurable_function_for_restricted_measure R X Y mu hm B _ hg.
apply: (@measurable_function_almost_equal R X Y (measure_restrict mu B)
  (measure_restrict_is_measure hm B) _ f hgn).
apply: (proj2 (restricted_almost_everywhere_iff mu B _)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hg))=> x [y hy] hb.
exists y; split=> //.
exact: (proj1 (@partial_function_zero_extension_on X Y zero B f x y hb) hy).
Qed.
