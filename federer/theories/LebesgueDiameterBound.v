(** The lower comparison in Federer (1969), 2.10.7, pp. 174–175, concluding
    H^1=L^1 on the real line. We use the already proved measure laws and
    segment-length characterization of 2.5.17, p. 111, to bound every
    diameter cover. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter
  MetricDiameterReal MeasureUP MeasureBasic MeasureIndexedCover
  NonnegativeSum LebesgueScalarMeasure MetricScaleEnvelopeUP MetricScaleEnvelope
  CaratheodoryLimitUP HausdorffLengthUP HausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lebesgue_scalar_diameter_bound]: the interval-hull lower
    estimate supporting Federer 2.10.7, pp. 174–175 The bound holds for
    arbitrary nonempty sets, without a measurability premise. *)
Lemma lebesgue_scalar_diameter_bound (R : realType) (A : set R) :
  A !=set0 -> lebesgue_scalar_measure A <=
    @extended_metric_diameter R [the metricType R of real_line_metric R] A.
Proof.
move=> hA.
pose d := @extended_metric_diameter R [the metricType R of real_line_metric R] A.
have hd := extended_metric_diameter_specification (X:=[the metricType R of real_line_metric R]) A.
change (lebesgue_scalar_measure A<=d).
case hdE: d=> [r| |]; last first.
- have h := metric_diameter_nonnegative hd; by rewrite -/d hdE in h.
- exact: leey.
- have hr : (0<=r)%R.
    have h := metric_diameter_nonnegative hd; by rewrite -/d hdE lee_fin in h.
  have hdist x y : A x -> A y -> (`|x-y|<=r)%R.
    move=> hx hy; have h := metric_diameter_upper hd hx hy.
    by rewrite real_line_metric_distanceE -/d hdE lee_fin in h.
  have hc := real_bounded_diameter_interval_hull hA hdist.
  have hb := @MeasureBasic.measure_mono R R _ (lebesgue_scalar_is_measure R)
    A `[inf A,(inf A+r)%R] hc.
  apply: le_trans hb _.
  have habound : (inf A<=inf A+r)%R by rewrite lerDl.
  by rewrite (lebesgue_scalar_segment habound) addrAC subrr add0r.
Qed.

(** Source for [lebesgue_below_hausdorff_length]: the
    lower inequality in the concluding H^1=L^1 assertion
    of Federer 2.10.7, p. 175. Countable
    subadditivity bounds each admissible diameter covering;
    no Borel condition on the test set is required. *)
Theorem lebesgue_below_hausdorff_length (R : realType) (A : set R) :
  lebesgue_scalar_measure A <=
    @hausdorff_length R [the metricType R of real_line_metric R] A.
Proof.
pose X := [the metricType R of real_line_metric R].
pose J := @nonempty_metric_sets R X.
pose S := fun j : J => val j.
pose c := fun j : J => extended_metric_diameter (val j).
pose nu := metric_scale_envelope S c 1.
have hn := @metric_scale_envelope_specification R X J S c 1.
have hlow : lebesgue_scalar_measure A<=nu A.
  apply: (metric_scale_envelope_greatest hn)=> G hG _ hcover.
  apply: le_trans (@measure_indexed_cover R R J
    _ (lebesgue_scalar_is_measure R) A G S hG hcover) _.
  apply: nonnegative_sum_mono=> j hj.
  exact: lebesgue_scalar_diameter_bound (set_valP j).
apply: le_trans hlow _.
exact (@caratheodory_limit_upper R X J S c (@hausdorff_length R X)
  (@hausdorff_length_specification R X) A 1 nu (ltr01 : 0<1) hn).
Qed.
