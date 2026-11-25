(** Federer (1969), 2.4.12, p. 87: countable measurability of finite-image
    approximants at p=infinity. The definition is Federer 2.3.4, p. 76. The
    supporting result below applies to any Borel map preserving the
    distinguished zero. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition MeasureUP BorelFunctionUP
  MeasurablePostcomposition CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableSubsets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_measurable_zero_postcomposition]: supporting
    nonzero-locus argument for Federer 2.4.12, p. 87 The new nonzero locus
    is a measurable subset of the old one because the postcomposition fixes
    zero; source measure need not be finite. *)
Lemma countably_measurable_zero_postcomposition (R : realType) (X : choiceType)
    (Y Z : topologicalType) (zeroY : Y) (zeroZ : Z)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) (a : Y -> Z) :
  closed [set z | z=zeroZ] -> a zeroY=zeroZ -> is_borel_function a ->
  is_countably_measure_measurable_function mu zeroY f ->
  is_countably_measure_measurable_function mu zeroZ (partial_function_postcompose f a).
Proof.
move=> hz ha haB hf.
have hmeas := @measurable_function_borel_postcomposition R X Y Z mu hm f a
  (countably_measurable_function_measurable hf) haB.
constructor=> //.
apply: (@measurable_subset_countably_measurable R X mu hm _ (partial_function_nonzero_locus zeroY f)
  (@measurable_function_nonzero_locus R X Z mu hm zeroZ _ hz hmeas) _
  (countably_measurable_function_locus hf)).
move=> x [z [[y [hy he]] hn]]; exists y; split=> // hy0.
apply: hn; by rewrite -he hy0 ha.
Qed.
