(** Federer (1969), 2.9.22, p. 168: the inequality for the integral of s'
    over inverse images. We expand the interval estimate through the
    derivative variation measure. The real-line Hausdorff identity already
    proved for 2.5.10 gives an equivalent diameter-cover route from
    intervals to arbitrary sets, in place of the book's
    open-interval/open-set approximation. This is a local proof-route
    departure, not a change in the resulting bound. No relevant Federer
    erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter
  MeasureUP MeasureBasic MeasurePushforward MeasureIndexedCover NonnegativeSum
  AtomlessIntervalHullBound MetricScaleEnvelopeUP MetricScaleEnvelope
  CaratheodoryLimitUP HausdorffLengthUP HausdorffLength HausdorffLengthReal LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_measure_below_lebesgue_from_diameters]:
    supporting interval-to-set extension in Federer 2.9.22, p. 168.
    Countable diameter covers and the already proved H^1=L^1 identity
    of 2.10.7, p. 175, extend a bound on every nonempty set to
    domination by Lebesgue measure on all subsets. This replaces the
    printed open approximation without assuming sets measurable. *)
Lemma real_measure_below_lebesgue_from_diameters (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (hm : is_measure mu) :
  (forall A, A !=set0 -> mu A<=@extended_metric_diameter R
    [the metricType R of real_line_metric R] A) ->
  forall A, mu A<=lebesgue_scalar_measure A.
Proof.
move=> hdiam A.
pose X := [the metricType R of real_line_metric R].
pose J := @nonempty_metric_sets R X.
pose S := fun j : J => val j.
pose c := fun j : J => extended_metric_diameter (val j).
pose nu := metric_scale_envelope S c 1.
have hn := @metric_scale_envelope_specification R X J S c 1.
have hlow : mu A<=nu A.
  apply: (metric_scale_envelope_greatest hn)=> G hG _ hcover.
  apply: le_trans (@measure_indexed_cover R X J mu hm A G S hG hcover) _.
  apply: nonnegative_sum_mono=> j hj; exact: hdiam (set_valP j).
have hh := @caratheodory_limit_upper R X J S c (@hausdorff_length R X)
  (@hausdorff_length_specification R X) A 1 nu (lte01 : (0<1)%E) hn.
rewrite hausdorff_length_real_eq_lebesgue in hh.
exact: le_trans hlow hh.
Qed.

(** Source for [monotone_atomless_measure_image_bound]: supporting
    form of the second integral inequality in Federer 2.9.22,
    p. 168. If a diffuse measure nu has segment mass at most
    s(b)-s(a) for nondecreasing s, its image under s is bounded
    by Lebesgue measure, on arbitrary sets. Null singleton masses
    are essential: jumps of s do not contribute derivative mass. *)
Theorem monotone_atomless_measure_image_bound (R : realType)
    (s : R -> R) (nu : set (real_line_metric R) -> \bar R)
    (hn : is_measure nu) :
  (forall a b, (a<=b)%R -> (s a<=s b)%R) ->
  (forall x, nu [set x]=0) ->
  (forall a b : R, measure_measurable nu `[a,b]) ->
  (forall a b : R, (a<=b)%R -> nu `[a,b]<=(s b-s a)%:E) ->
  forall A, nu (s @^-1` A)<=lebesgue_scalar_measure A.
Proof.
move=> hs hz hmeas hseg.
have him := @measure_pushforward_is_measure R (real_line_metric R)
  (real_line_metric R) s nu hn.
apply: (@real_measure_below_lebesgue_from_diameters R _ him)=> A hA.
pose M := @extended_metric_diameter R [the metricType R of real_line_metric R] A.
have hd := @extended_metric_diameter_specification R [the metricType R of real_line_metric R] A.
change (nu (s @^-1` A)<=M).
apply: (@atomless_real_interval_hull_bound R nu hn (s @^-1` A) M hz hmeas
  (metric_diameter_nonnegative hd))=> a b ha hb hab.
apply: le_trans (hseg a b hab) _.
have he : (s b-s a)%:E=(`|s b-s a|)%:E.
  by rewrite ger0_norm // subr_ge0 hs.
rewrite he.
have h := @metric_diameter_upper R [the metricType R of real_line_metric R]
  A M hd (s b) (s a) hb ha.
by rewrite real_line_metric_distanceE in h.
Qed.
