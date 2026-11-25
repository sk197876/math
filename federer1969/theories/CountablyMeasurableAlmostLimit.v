(** Supporting countable-measurability facts for Federer (1969), 2.4.12, pp.
    86–87, especially the L-infinity completeness claim. The definition is
    Federer 2.3.4, p. 76. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP MeasurableFunctionUP
  MeasureUP MeasureAlmostUP CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableSubsets CountablyMeasurableUnions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_almost_limit]: supporting preservation
    of the countable-measurability condition in the completeness assertion
    of Federer 2.4.12, p. 87 The target need only be a metric space with a
    distinguished zero. *)
Theorem countably_measurable_almost_limit (R : realType) (X : choiceType)
    (Y : metricType R) (zero : Y) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X Y) (g : partial_function X Y) :
  closed [set y | y=zero] ->
  (forall n, is_countably_measure_measurable_function mu zero (f n)) ->
  is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  is_countably_measure_measurable_function mu zero g.
Proof.
move=> hz hf hg hl; constructor=> //.
pose B := \bigcup_n partial_function_nonzero_locus zero (f n).
pose E := ~` partial_function_limit_locus f g.
have hB : measure_countably_measurable mu B.
  apply: countably_measurable_countable_union (countableP setT) _=> n.
  exact: countably_measurable_function_locus (hf n).
have hE : measure_countably_measurable mu E := null_set_countably_measurable hm hl.
apply: (@measurable_subset_countably_measurable R X mu hm _ (B `|` E) _ _
  (countably_measurable_binary_union hB hE)).
- exact (@measurable_function_nonzero_locus R X Y mu hm zero g hz hg).
- move=> x [y [hy hy0]]; have [hxB|hxB] := pselect (B x); first by left.
  right; move=> hxlim.
  case: hxlim=> u [z [hu [hz' hlim]]].
  have huz n : u n = zero.
    apply: contrapT=> hn; apply: hxB; exists n=> //; exists (u n); by split.
  have he : z=y := partial_function_single_valued hz' hy.
  have huconst : u=(fun _ : nat => zero) by apply: functional_extensionality_dep.
  have hlim0 : u @ \oo --> zero by rewrite huconst; exact: cvg_cst.
  have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
  have PF : ProperFilter (u @ \oo) := @fmap_proper_filter nat Y u \oo PF0.
  have he0 := @cvg_unique Y (@metric_hausdorff R Y) (u @ \oo) PF z zero hlim hlim0.
  apply: hy0; by rewrite -he he0.
Qed.
