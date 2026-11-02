(** Federer (1969), 3.1.4, p. 215: the translated slices
    used in the pointwise Fubini argument are measurable outside a
    null set of base points. This qualification is derived from the
    original measurable function and cutoff set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanPrefixTranslation EuclideanPrefixSliceMeasurability
  EuclideanPrefixCutoffs RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasurableFunctionUP MeasureUP MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic ProductSections MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section GoodBases.
Variable R : realType.
Variable m : nat.
Variable i : 'I_m.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variables f g : E m -> R^o.
Variable B : set (E m).

(** Source for [coordinate_section_good_bases]: the supporting
    conull set where the f, g_i and B slices in the Fubini estimate
    of Federer 3.1.4, p. 215, are measurable. *)
Definition coordinate_section_good_bases : set (E m) := [set a |
  is_measure_measurable_function (@euclidean_lebesgue_measure R i)
    (partial_function_precompose (@euclidean_prefix_translation R m i a)
      (partial_function_total (fun x=>(f x : real_line_metric R)))) /\
  is_measure_measurable_function (@euclidean_lebesgue_measure R (i+1))
    (partial_function_precompose (@euclidean_prefix_translation R m (i+1) a)
      (partial_function_total (fun x=>(f x : real_line_metric R)))) /\
  is_measure_measurable_function (@euclidean_lebesgue_measure R i)
    (partial_function_precompose (@euclidean_prefix_translation R m i a)
      (partial_function_total (fun x=>(g x : real_line_metric R)))) /\
  measure_measurable (@euclidean_lebesgue_measure R i)
    ((@euclidean_prefix_translation R m i a) @^-1` B)].

(** Source for [coordinate_section_good_bases_conull]:
    the needed slice-measurability qualification for Federer 3.1.4,
    p. 215, from 3.1.3 and Fubini, without an added hypothesis on f. *)
Theorem coordinate_section_good_bases_conull :
  @is_measure_measurable_function R [the choiceType of E m]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total f) ->
  @is_measure_measurable_function R [the choiceType of E m]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) ->
  measure_measurable (@euclidean_lebesgue_measure R m) B ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m) coordinate_section_good_bases.
Proof.
move=> hf hg hB.
have hi : (i<=m)%N := leqW (ltn_ord i).
have hj : (i+1<=m)%N by rewrite addn1; exact: ltn_ord.
have h0 := @euclidean_almost_measurable_prefix_slices R m i
  (partial_function_total (fun x=>(f x : real_line_metric R))) hi hf.
have h1 := @euclidean_almost_measurable_prefix_slices R m (i+1)
  (partial_function_total (fun x=>(f x : real_line_metric R))) hj hf.
have h2 := @euclidean_almost_measurable_prefix_slices R m i
  (partial_function_total (fun x=>(g x : real_line_metric R))) hi hg.
have h3 := @euclidean_almost_measurable_prefix_set_slices R m i B hi hB.
exact: (measure_almost_everywhere_and (euclidean_lebesgue_is_measure R m) h0
  (measure_almost_everywhere_and (euclidean_lebesgue_is_measure R m) h1
    (measure_almost_everywhere_and (euclidean_lebesgue_is_measure R m) h2 h3))).
Qed.

(** Source for [coordinate_section_good_bases_measurable]:
    the conull slice qualification is measurable by 2.1.3(6),
    p. 55, supporting the refined cutoffs in 3.1.4, p. 215. *)
Lemma coordinate_section_good_bases_measurable :
  @is_measure_measurable_function R [the choiceType of E m]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total f) ->
  @is_measure_measurable_function R [the choiceType of E m]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) ->
  measure_measurable (@euclidean_lebesgue_measure R m) B ->
  measure_measurable (@euclidean_lebesgue_measure R m) coordinate_section_good_bases.
Proof.
move=> hf hg hB.
have hn := coordinate_section_good_bases_conull hf hg hB.
have hh := measure_measurable_complement
  (measure_null_measurable (euclidean_lebesgue_is_measure R m) hn).
by rewrite setCK in hh.
Qed.

(** Source for [coordinate_good_base_variation_measurable]:
    the Z section in Federer 3.1.4, pp. 214–215, is
    measurable at every retained good base. The weak threshold is
    the correction on erratum p. 4, book p. 214 line 24. *)
Lemma coordinate_good_base_variation_measurable a e :
  coordinate_section_good_bases a ->
  measure_measurable (@euclidean_lebesgue_measure R i)
    (product_vertical_section (@prefix_slice_variation_exception R m i B g e) a).
Proof.
move=> [_ [_ [hg hB]]].
pose P := partial_function_precompose (@euclidean_prefix_translation R m i a)
  (partial_function_total (fun x=>(g x : real_line_metric R))).
pose W : set (real_line_metric R) := [set y | mdist (g a : real_line_metric R) y < e].
have hW : open W := metric_open_ball_open _ _.
have hv := measure_measurable_complement (measurable_function_open_preimage hg hW).
have he : product_vertical_section (@prefix_slice_variation_exception R m i B g e) a=
    (~` ((@euclidean_prefix_translation R m i a) @^-1` B)) `|`
    (~` partial_function_preimage P W).
  apply/seteqP; split=> z.
  - move=> [hn|hb]; first by left.
    right.
    move=> [v [hv0 hw]].
    change (g (euclidean_prefix_translation a z)=v) in hv0.
    move: hw; rewrite /W /= -hv0
      real_line_metric_distanceE distrC ltNge hb; by [].
  - move=> [hn|hn]; first by left.
    right; rewrite leNgt; apply/negP=> hg0; apply: hn.
    exists (g (euclidean_prefix_translation a z)); split=> //.
    by rewrite /W /= real_line_metric_distanceE distrC.
rewrite he; exact: (measure_measurable_union (euclidean_lebesgue_is_measure R i)
  (measure_measurable_complement hB) hv).
Qed.
End GoodBases.
