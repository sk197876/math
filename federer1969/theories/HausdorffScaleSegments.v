(** The interval subdivision estimate supporting Federer (1969), 2.10.7, pp.
    174–175, whose last sentence identifies Hausdorff length and Lebesgue
    measure on R. We use closed binary subdivisions and the already proved
    Lebesgue lower bound; this is a different elementary realization of the
    book's arbitrary-small-mesh argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter
  MetricDiameterReal RealSegmentBisection MeasureUP MeasureSplit
  MetricScaleEnvelopeUP MetricScaleCutoffCost HausdorffLengthUP
  HausdorffScaleSingleCover SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_scale_binary_segment_bound]:
    supporting finite small-mesh bound in Federer 2.10.7,
    pp. 174–175. Repeated bisection supplies a cover
    whose total length is exactly b-a, including a=b. *)
Lemma hausdorff_scale_binary_segment_bound (R : realType)
    (delta : \bar R) (nu : set R -> \bar R) :
  @is_metric_scale_envelope R [the metricType R of real_line_metric R]
    (@nonempty_metric_sets R [the metricType R of real_line_metric R])
    (fun j => val j) (fun j => extended_metric_diameter (val j)) delta nu ->
  forall n a b, a<=b -> (((b-a)*(2^-1)^+n)%:E<=delta)%E ->
    (nu `[a,b]<=(b-a)%:E)%E.
Proof.
move=> hn.
have hmu : is_measure nu.
  apply: (metric_scale_envelope_is_measure hn)=> j.
  exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
elim=> [|n ih] a b hab hmesh.
- rewrite expr0 mulr1 in hmesh.
  have hne : `[a,b] !=set0.
    exists a; by rewrite /= in_itv /= lexx hab.
  have hd := extended_metric_diameter_segment hab.
  have hb := @hausdorff_scale_single_cover R [the metricType R of real_line_metric R]
    delta nu hn `[a,b] hne.
  by rewrite hd in hb; exact: hb hmesh.
- have [hal [hlb [hla hbl]]] := real_segment_midpoint_lengths hab.
  set m := a+(b-a)/2 in hal hlb hla hbl *.
  have hhalf : (((b-a)/2*(2^-1)^+n)%:E<=delta)%E.
    by rewrite exprS mulrA in hmesh.
  have hleft := ih a m hal.
  have hright := ih m b hlb.
  rewrite hla in hleft; rewrite hbl in hright.
  have hc := @measure_binary_cover R R nu hmu
    `[a,b] `[a,m] `[m,b] (@real_segment_midpoint_cover R a b m).
  apply: le_trans hc _.
  have hh := leeD (hleft hhalf) (hright hhalf).
  by rewrite -EFinD real_segment_half_sum in hh.
Qed.

(** Source for [hausdorff_scale_segment_bound]: every
    positive size approximation assigns a segment at most its
    length, the small-mesh part of Federer 2.10.7,
    pp. 174–175. Positive infinite cutoffs and
    zero-length segments are included explicitly. *)
Theorem hausdorff_scale_segment_bound (R : realType)
    (delta : \bar R) (nu : set R -> \bar R) :
  @is_metric_scale_envelope R [the metricType R of real_line_metric R]
    (@nonempty_metric_sets R [the metricType R of real_line_metric R])
    (fun j => val j) (fun j => extended_metric_diameter (val j)) delta nu ->
  (0<delta)%E -> forall a b, a<=b -> (nu `[a,b]<=(b-a)%:E)%E.
Proof.
move=> hn hp a b hab.
have hlength : 0<=b-a by rewrite subr_ge0.
case: delta hp hn=> [d| |] hp hn.
- rewrite lte_fin in hp.
  have [hz|hz] := eqVneq (b-a) 0.
    apply: (@hausdorff_scale_binary_segment_bound R d%:E nu hn 0 a b hab).
    by rewrite hz mul0r lee_fin; exact: ltW hp.
  have hpos : 0<b-a by rewrite lt_neqAle eq_sym hz hlength.
  have he : 0<d/(b-a) by rewrite divr_gt0.
  have [n hsmall] := sequence_inverse_power_small he.
  apply: (@hausdorff_scale_binary_segment_bound R d%:E nu hn n a b hab).
  rewrite lee_fin; apply: ltW.
  by move: hsmall; rewrite ltr_pdivlMr // mulrC.
- apply: (@hausdorff_scale_binary_segment_bound R +oo nu hn 0 a b hab).
  exact: leey.
- by move: hp; rewrite ltNge leNye.
Qed.
