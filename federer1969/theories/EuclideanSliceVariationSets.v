(** Federer (1969), 3.1.4, p. 214: the exceptional prefix
    shifts Z leave B or change g by at least the chosen tolerance.
    The weak inequality follows erratum p. 4, book p. 214 line 24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanSliceTranslation EuclideanSliceMeasurability EuclideanEpimorphismMeasurable
  RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  ProductMeasure ProductFunctionMeasurability ProductSections MeasureUP MeasureFiniteClosure
  PushforwardMeasurableSets MeasurableFunctionUP MeasurableRealArithmetic MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section VariationSets.
Variable R : realType.
Variables k l : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R (k+l))).
Local Notation Z := (inner_metric_space (@euclidean_inner_productP R k)).
Variable B : set X.
Variable g : X -> R^o.
Variable e : R.

(** Source for [euclidean_slice_variation_exception]: the two
    alternatives defining Z in Federer 3.1.4, p. 214, before
    restriction to |z|<r. The derivative-variation inequality follows
    the corrected weak threshold in erratum p. 4, book p. 214 line 24. *)
Definition euclidean_slice_variation_exception : set (X*Z) :=
  [set az | ~B (@euclidean_slice_translation R k l az.1 az.2) \/
    e<=`|g (@euclidean_slice_translation R k l az.1 az.2)-g az.1|].

(** Source for [euclidean_slice_variation_exception_measurable]:
    the measurable Z-family needed for C in Federer 3.1.4,
    pp. 214–215, by 3.1.3(3) and scalar measurable arithmetic. *)
Theorem euclidean_slice_variation_exception_measurable :
  measure_measurable (@euclidean_lebesgue_measure R (k+l)) B ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R (k+l))
    (partial_function_total g) ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R (k+l))
    (euclidean_lebesgue_is_measure R k)) euclidean_slice_variation_exception.
Proof.
move=> hB hg.
pose ha := euclidean_lebesgue_is_measure R (k+l).
pose hb := euclidean_lebesgue_is_measure R k.
pose mu := product_measure ha hb.
pose hm := product_measure_is_measure ha hb.
pose shift := fun az : X*Z=>@euclidean_slice_translation R k l az.1 az.2.
have hpre : measure_measurable mu (shift @^-1` B).
  rewrite /mu -euclidean_block_measure.
  apply: pushforward_measurable_from_preimage.
  change (measure_measurable (@euclidean_lebesgue_measure R ((k+l)+k))
    ((@euclidean_slice_sum R k l) @^-1` B)).
  exact: euclidean_epimorphism_preimage_measurable (@euclidean_slice_sum_surjective R k l) hB.
pose G := partial_function_precompose shift (partial_function_total g).
pose H := partial_function_total (fun az : X*Z=>(g az.1 : real_line_metric R)).
pose D := partial_real_function_subtract G H.
have hG := euclidean_translated_slices_measurable hg.
have hH := product_measurable_first_function ha hb hg.
have hD := @measurable_real_function_subtract R [the choiceType of (X*Z)%type] mu hm G H hG hH.
pose U := [set y : real_line_metric R | `|y|<e].
have hU : open U.
  have he : U=[set y : real_line_metric R | mdist (0 : real_line_metric R) y<e].
    by apply/seteqP; split=> y; rewrite /U /= real_line_metric_distanceE sub0r normrN.
  rewrite he; exact: metric_open_ball_open.
have hv := measure_measurable_complement (measurable_function_open_preimage hD hU).
have he : euclidean_slice_variation_exception=
    (~` (shift @^-1` B)) `|` (~` partial_function_preimage D U).
  apply/seteqP; split; move=> [a z] hx.
  - case: hx=> [hbz|hvar]; first by left.
    right.
    move=> [v [[[u w] [[hu hw] hvw]] hUv]].
    change (g (shift (a,z))=u) in hu; change (g a=w) in hw; change (u-w=v) in hvw.
    move: hUv; rewrite /U /= -hvw -hu -hw ltNge hvar; by [].
  - case: hx=> [hbz|hvar]; first by left.
    right; rewrite leNgt; apply/negP=> hgood; apply: hvar.
    exists (g (shift (a,z))-g a); split=> //.
    exists (g (shift (a,z)),g a); by split=> //; split.
rewrite he; exact: (measure_measurable_union hm (measure_measurable_complement hpre) hv).
Qed.
End VariationSets.
