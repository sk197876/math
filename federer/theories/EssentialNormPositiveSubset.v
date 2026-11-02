(** Federer (1969), 2.4.16, p. 90: the set A1 may be chosen inside {|f|>t}
    for 0<t<phi_infinity(f). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureGauge MeasureEssentialNorm CountablyMeasurableUP
  CountablyMeasurableSubsets MeasurableNormSuperlevels PositiveFiniteMeasureSubset.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [essential_norm_positive_finite_superlevel_subset]:
    the finite positive-measure choice A1 in Federer 2.4.16,
    p. 90, with countable measurability explicitly used. *)
Lemma essential_norm_positive_finite_superlevel_subset (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (t : R) :
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  (0 < t)%R -> t%:E < measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f) ->
  exists B, measure_measurable mu B /\ 0 < mu B /\ mu B < +oo /\
    forall x, B x -> (t < `|f x|)%R.
Proof.
move=> hf ht htn.
pose A := partial_norm_superlevel (fun y : R => `|y|%R) (partial_function_total f) t%:E.
have hA := @measurable_norm_superlevel R X R^o _ (scalar_absolute_value_norm R)
  mu hm (partial_function_total f) (countably_measurable_function_measurable hf) t.
have hAc : measure_countably_measurable mu A.
  apply: (@measurable_subset_countably_measurable R X mu hm A _ hA _
    (countably_measurable_function_locus hf)).
  move=> x [y [hy hty]]; exists y; split=> //.
  by move=> hz; move: hty; rewrite /= hz normr0 lte_fin ltNge (ltW ht).
have hpos : 0 < mu A.
  rewrite lt_neqAle eq_sym (measure_nonnegative hm) andbT; apply/eqP=> hz.
  have hn : measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f) <= t%:E.
    apply: measure_essential_norm_bound; split=> //; by rewrite lee_fin; exact: ltW ht.
  by move: htn; rewrite ltNge hn.
have [B [hBA [hB [hBp hBf]]]] := @positive_countably_measurable_finite_subset R X mu hm A hAc hpos.
exists B; split=> //; split=> //; split=> //.
move=> x hx; have [y [hy hty]] := hBA x hx.
by move: hty; rewrite /= -(hy : f x=y) lte_fin.
Qed.
