(** Federer (1969), 2.4.9, p. 85, final sentence of the proof: domination by
    a summable function implies summability. The supporting
    absolute-summability criterion follows from 2.4.4(2), (5), (6), (8), pp.
    82–83. Source context: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralNegation MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableExtendedAbsolute PartialExtendedOrderLoci PartialAbsolutePartsGraph
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralAbsolute
  MeasureIntegralNegationLaw MeasureUpperIntegralMonotone MeasurableFiniteBoundIntegrable
  MeasureIntegralComparison MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_absolute_order]: supporting
    pointwise bound by absolute value for the summability
    inference in Federer 2.4.9, p. 85. *)
Lemma partial_function_absolute_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_extended_le_locus f (partial_extended_function_absolute_value f)) /\
  measure_almost_everywhere mu (partial_extended_le_locus (partial_extended_function_negate f)
    (partial_extended_function_absolute_value f)).
Proof.
move=> hd; split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
  exists y,`|y|; split=> //; split; first by exists y; split.
  exact: lee_abs.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
  exists (-y),`|y|; split; first by exists y; split.
  split; first by exists y; split.
  by move: (lee_abs (-y)); rewrite abseN.
Qed.

(** Source for [measure_absolute_summable_implies_summable]: supporting
    summability criterion used in Federer 2.4.9, p. 85, last sentence We
    equivalently use the two bounds f,-f <= |f|. *)
Lemma measure_absolute_summable_implies_summable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  is_measure_summable mu (partial_extended_function_absolute_value f) -> is_measure_summable mu f.
Proof.
move=> hf [b hb].
have [hpos hneg] := @partial_function_absolute_order R X mu hm f (measurable_function_domain hf).
have eb := @measure_upper_integral_unique R X mu _ _ b%:E
  (measure_upper_integral_specification mu _) hb.2.1.
have huf : measure_upper_integral mu f < +oo.
  apply: le_lt_trans (@measure_upper_integral_monotone R X mu hm _ _ hpos) _.
  by rewrite eb ltry.
have [a ha] := @measurable_finite_upper_integrable R X mu hm f hf huf.
have hpa := @measure_integral_monotone R X mu hm _ _ a b%:E ha hb hpos.
have hna := @measure_integral_monotone R X mu hm _ _ (-a) b%:E
  (@measure_integral_negation R X mu hm f a ha) hb hneg.
have hfin : a \is a fin_num.
  apply: fin_real; apply/andP; split.
  - have hn' : -a < +oo := le_lt_trans hna (ltry b).
    by move: hn'; rewrite lteNl.
  - exact: le_lt_trans hpa (ltry b).
exists (fine a); by rewrite fineK.
Qed.

(** Source for [measure_dominated_summable]: the domination inference in
    Federer 2.4.9, p. 85, last proof sentence We allow the bound to hold
    almost everywhere. *)
Lemma measure_dominated_summable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f h : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_summable mu h ->
  measure_almost_everywhere mu (partial_extended_le_locus (partial_extended_function_absolute_value f) h) ->
  is_measure_summable mu f /\ is_measure_summable mu (partial_extended_function_absolute_value f).
Proof.
move=> hf [c hc] hdom.
have haf := @measurable_extended_absolute_value R X mu hm f hf.
have hnon : measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_extended_function_absolute_value f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
  move=> x [y hy]; exists `|y|; split; first by exists y; split.
  exact: abse_ge0.
have [hb hB] := @nonnegative_measurable_function_integral R X mu hm _ haf hnon.
have hbc := @measure_integral_monotone R X mu hm _ _ _ c%:E hb hc hdom.
have hfin : measure_lower_integral mu (partial_extended_function_absolute_value f) \is a fin_num.
  rewrite (ge0_fin_numE hB); exact: le_lt_trans hbc (ltry c).
have habs : is_measure_summable mu (partial_extended_function_absolute_value f).
  exists (fine (measure_lower_integral mu (partial_extended_function_absolute_value f))).
  by rewrite fineK.
split=> //; exact (@measure_absolute_summable_implies_summable R X mu hm f hf habs).
Qed.
