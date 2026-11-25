(** Federer (1969), 2.10.46, p. 203: the first projected-volume estimate
    follows from Fubini and the isodiametric inequality. This supporting
    form applies to a measurable set with measurable projection. Compact
    sets satisfy those premises, as do the relevant analytic images. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  OrthogonalProjectionChartUP ProjectionChartFubini ProjectionChartFibres
  EuclideanBlockCoordinates EuclideanLebesgueDimensions ProductSections
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureIntegralUP MeasureIntegralComparison
  PartialFunctionBasic PartialExtendedOrderLoci CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureExtendedCharacteristicIntegral MetricDiameterUP MetricDiameter
  HausdorffDiameterCost ExtendedSupremumPowers EuclideanIsodiametric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SectionBound.
Variable R : realType.
Variables m k : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variables p : {linear R_n R (m+k) -> R_n R k}.
Variables f g : {linear R_n R (m+k) -> R_n R (m+k)}.
Hypothesis hc : is_orthogonal_projection_chart p f g.
Local Notation H := ((g : E (m+k) -> E (m+k)) \o (@euclidean_block_join R m k)).
Local Notation Leb n := (@euclidean_lebesgue_measure R n).

(** Source for [projection_chart_fibre_volume_bound]: supporting
    application of the isodiametric inequality to each fibre
    in 2.10.46, p. 203, including empty fibres. *)
Lemma projection_chart_fibre_volume_bound (S : set (E (m+k))) (y : E k) :
  (Leb m (product_horizontal_section (H @^-1` S) y)<=hausdorff_diameter_cost m S)%E.
Proof.
pose A := product_horizontal_section (H @^-1` S) y.
have [he|hne] := eqVneq A set0.
  rewrite /A in he; rewrite he (measure_empty (euclidean_lebesgue_is_measure R m)).
  exact: hausdorff_diameter_cost_nonnegative.
apply: le_trans (@lebesgue_isodiametric_bound R m A ((set0P A).1 hne)) _.
rewrite /hausdorff_diameter_cost /hausdorff_power_cost.
apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R m).
apply: nonnegative_extended_power_monotone.
- exact: metric_diameter_nonnegative (extended_metric_diameter_specification A).
- exact (@projection_chart_fibre_diameter R m k p f g hc S y).
Qed.

(** Source for [projection_chart_volume_support_bound]: supporting
    Fubini–isodiametric estimate in 2.10.46, p. 203:
    volume is at most the volume of a measurable superset
    of the projection times alpha(m)2^(-m)
    times diameter to the power m. The explicit measurability
    premises allow the use of the proved Fubini theorem.
    Infinite diameter and zero-dimensional fibres are included. *)
Theorem projection_chart_volume_support_bound (S : set (E (m+k))) (C : set (E k)) :
  measure_measurable (Leb (m+k)) S -> measure_measurable (Leb k) C ->
  p @` S `<=` C ->
  (Leb (m+k) S<=Leb k C*hausdorff_diameter_cost m S)%E.
Proof.
move=> hS hP hPC.
pose c := hausdorff_diameter_cost m S.
pose s := @CharacteristicFunction.value R (E k) C.
have hs : is_characteristic_function C s := CharacteristicFunction.laws R C.
have hi := @projection_chart_section_integral R m k p f g hc S hS.
have hj := @measure_nonnegative_extended_characteristic_integral R [the choiceType of E k]
  (Leb k) (euclidean_lebesgue_is_measure R k) C s c hs hP
  (hausdorff_diameter_cost_nonnegative m S).
rewrite muleC in hj.
apply: (@measure_integral_monotone R [the choiceType of E k] (Leb k)
  (euclidean_lebesgue_is_measure R k) _ _ _ _ hi hj).
apply: (@measure_almost_everywhere_mono R [the choiceType of E k] (Leb k)
  (euclidean_lebesgue_is_measure R k) setT _ _
  (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R k))).
move=> y _; exists (Leb m (product_horizontal_section (H @^-1` S) y)), (c*(s y)%:E)%E.
split=> //; split=> //.
case: (pselect (C y))=> hy.
- rewrite (characteristic_on_set hs hy) mule1; exact (projection_chart_fibre_volume_bound S y).
- have hout : ~ (p @` S) y by move=> hpS; apply: hy; exact: hPC.
  rewrite (characteristic_off_set hs hy) mule0
    (@projection_chart_fibre_outside_image R m k p f g hc S y hout) (measure_empty (euclidean_lebesgue_is_measure R m)).
  exact: lexx.
Qed.
(** Source for [projection_chart_volume_bound]: the projected-volume
    estimate of 2.10.46, p. 203, for measurable sets with
    measurable projection, as a consequence of the support bound. *)
Theorem projection_chart_volume_bound (S : set (E (m+k))) :
  measure_measurable (Leb (m+k)) S -> measure_measurable (Leb k) (p @` S) ->
  (Leb (m+k) S<=Leb k (p @` S)*hausdorff_diameter_cost m S)%E.
Proof. move=> hS hP; exact: projection_chart_volume_support_bound hS hP (subset_refl _). Qed.
End SectionBound.
