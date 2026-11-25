(** Federer (1969), 2.6.2(4), p. 115, parenthesis: summability implies the
    countable-measurability hypothesis. Here the scalar function may take
    infinite values on a null set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealReciprocalBounds PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP CountableOrderIntervals
  PartialExtendedOrderLoci PartialExtendedArithmetic PartialAbsolutePartsGraph MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralAbsolute MeasureNonnegativeThresholdBound
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_summable_countably_measurable]:
    supporting nonnegative case of the parenthesis in Federer
    2.6.2(4), p. 115. Positive reciprocal superlevels
    have finite measure by the characteristic lower-integral bound;
    their union is the nonzero locus. *)
Lemma nonnegative_summable_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  is_measure_integral mu f a%:E ->
  (forall x y, partial_function_graph f x y -> 0 <= y) ->
  is_countably_measure_measurable_function mu (0 : extended_real_line R) f.
Proof.
move=> hi hp; constructor; first exact hi.1.
pose A n := partial_function_preimage f [set y | (((n.+1)%:R : R)^-1)%:E < y].
have hA n : measure_measurable mu (A n).
  apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hi.1).
  exact: order_strict_upper_ray_open.
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hi.1)).
  move=> x [y hy]; exists y; split=> //; exact: hp hy.
apply: (countably_measurable_sequence_iff hm _).2; exists A; split.
- apply/seteqP; split=> x.
  + move=> [y [hy hy0]]; have hypos : 0 < y by rewrite lt_def (hp x y hy) andbT; exact/eqP.
    have hex : exists n, (((n.+1)%:R : R)^-1)%:E < y.
      clear hy hy0.
      case: y hypos=> [r| |] hr; last by [].
      * have [n hn] := positive_reciprocal_nat_small hr; by exists n.
      * exists 0%N; exact: ltry.
    have [n hn] := hex; exists n=> //; by exists y.
  + move=> [n _ [y [hy hn]]]; exists y; split=> // => ey.
    move: hn; rewrite /= ey lte_fin ltNge invr_ge0 ler0n; by [].
- move=> n; split; first exact: hA.
  have hr : (0 < ((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have ht x : A n x -> exists y, partial_function_graph f x y /\ (((n.+1)%:R : R)^-1)%:E <= y.
    move=> [y [hy hn]]; exists y; split=> //; exact: ltW hn.
  have hb := @nonnegative_threshold_lower_integral_bound R X mu hm (A n) ((n.+1)%:R)^-1 f
    (hA n) (ltW hr) ht hpos.
  have he := @measure_lower_integral_unique R X mu f _ a%:E (measure_lower_integral_specification mu f) hi.2.2.
  rewrite he in hb.
  case hmu : (mu (A n))=> [r| |]; rewrite ?ltry ?ltNyy //.
  move: hb; by rewrite hmu gt0_muley ?lte_fin // leNgt ltry.
Qed.

(** Source for [measure_summable_countably_measurable]: complete
    summability parenthesis of Federer 2.6.2(4), p. 115,
    by absolute summability 2.4.4(8), p. 82. The
    nonzero loci of f and its absolute value coincide, even
    when f has infinite values or a proper conull domain. *)
Theorem measure_summable_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_summable mu f ->
  is_countably_measure_measurable_function mu (0 : extended_real_line R) f.
Proof.
move=> hf; have [b hb] := @measure_summable_absolute_value R X mu hm f hf.
have hp x y : partial_function_graph (partial_extended_function_absolute_value f) x y -> 0 <= y.
  move=> [z [_ <-]]; exact: abse_ge0.
have hc := @nonnegative_summable_countably_measurable R X mu hm _ b hb hp.
constructor; first by have [a ha] := hf; exact ha.1.
have he : partial_function_nonzero_locus 0 f =
    partial_function_nonzero_locus 0 (partial_extended_function_absolute_value f).
  apply/seteqP; split=> x.
  - move=> [y [hy hn]]; exists `|y|; split; first by exists y; split.
    move/eqP; rewrite abse_eq0; move/eqP; exact hn.
  - move=> [y [[z [hz <-]] hn]]; exists z; split=> // => ez.
    apply: hn; by rewrite ez abse0.
rewrite he; exact: countably_measurable_function_locus hc.
Qed.
