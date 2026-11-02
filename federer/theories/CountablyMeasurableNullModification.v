(** Federer (1969), 2.3.4, p. 76, applied to the null modifications in the
    proof of 2.6.2(4), p. 117: countable measurability survives an
    almost-equal measurable replacement, since its new nonzero locus lies in
    the old nonzero locus plus a null set. this is a supporting consequence,
    not a separately stated theorem there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostEquality MeasurableFunctionUP
  CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableSubsets CountablyMeasurableUnions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_zero_closed]: supporting order-
    topology fact for the zero locus in Federer 2.3.4,
    p. 76, with the extended-real topology of 2.1.1, p. 51. *)
Lemma extended_real_zero_closed (R : realType) : closed [set y : extended_real_line R | y = 0].
Proof.
have he : [set y : extended_real_line R | y = 0] = [set y | y <= 0] `&` [set y | 0 <= y].
  apply/seteqP; split.
  - move=> y ->; split; exact: lexx.
  - move=> y [hy hz]; apply/eqP; by rewrite eq_le hy hz.
rewrite he; apply: closedI; [exact: order_closed_lower_ray_closed|exact: order_closed_upper_ray_closed].
Qed.

(** Source for [countably_measurable_function_almost_equal]:
    supporting null-modification consequence of Federer 2.3.4,
    p. 76, used to preserve the exact support hypothesis
    of 2.6.2(4), p. 115. No ambient sigma-finiteness is required. *)
Lemma countably_measurable_function_almost_equal (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y)
    (f g : partial_function X Y) :
  closed [set y | y = zero] -> is_countably_measure_measurable_function mu zero f ->
  is_measure_measurable_function mu g -> measure_almost_equal mu f g ->
  is_countably_measure_measurable_function mu zero g.
Proof.
move=> hz hf hg he; constructor=> //.
pose N := ~` partial_function_agreement f g.
have hN : measure_countably_measurable mu N := null_set_countably_measurable hm he.
have hU := countably_measurable_binary_union (countably_measurable_function_locus hf) hN.
apply: (@measurable_subset_countably_measurable R X mu hm _ _
  (@measurable_function_nonzero_locus R X Y mu hm zero g hz hg) _ hU).
move=> x [y [hy hy0]]; case: (pselect (partial_function_agreement f g x))=> [[z [hzf hzg]]|hn].
- left; exists z; split=> //; have ez := partial_function_single_valued hzg hy.
  by rewrite ez.
- by right.
Qed.
