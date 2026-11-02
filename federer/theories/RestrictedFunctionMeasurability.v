(** Federer (1969), 2.5.10, p. 101, first paragraph: supporting comparison
    of functions for a measure and its restriction. The zero extension is
    2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure MeasureSplit
  MeasurableFunctionUP MeasurableZeroExtension MeasurableRestrictionTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_function_for_restricted_measure]: supporting
    restriction step in Federer 2.5.10, p. 101 The restricting set is
    arbitrary. *)
Lemma measurable_function_for_restricted_measure (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (f : partial_function X Y) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function (measure_restrict mu B) f.
Proof.
move=> hf; constructor.
- apply: (@measure_null_subset R X mu hm _ _ _ (measurable_function_domain hf)).
  by move=> x [_ hx].
- move=> U hU; exact: measure_restrict_measurable (measurable_function_open_preimage hf hU).
Qed.

(** Source for [restricted_measurable_zero_extension]: supporting return
    from a local density to the original measure in Federer 2.5.10, p. 101
    Only measurability for the restricted measure is assumed. *)
Lemma restricted_measurable_zero_extension (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y)
    (B : set X) (f : partial_function X Y) :
  measure_measurable mu B -> is_measure_measurable_function (measure_restrict mu B) f ->
  is_measure_measurable_function mu (partial_function_zero_extension zero B f).
Proof.
move=> hB hf; constructor.
- apply: (proj1 (@zero_extension_relative_domain R X Y mu zero B f)).
  exact: measurable_function_domain hf.
- move=> U hU; rewrite partial_zero_extension_preimage.
  apply: (@measure_measurable_union R X mu hm).
  + rewrite setIC; exact: (@measurable_restriction_intersection_transfer R X mu hm B _ hB
      (measurable_function_open_preimage hf hU)).
  + case: (pselect (U zero))=> hz.
    * have he : [set x | ~ B x /\ U zero]=~` B by apply/seteqP; split=> x; [move=> []|move=> hx; split].
      rewrite he; exact: measure_measurable_complement hB.
    * have he : [set x | ~ B x /\ U zero]=set0.
        apply/seteqP; split=> [x [_ hx]|x []]; exact: hz hx.
      rewrite he; exact: measure_measurable_empty hm.
Qed.
