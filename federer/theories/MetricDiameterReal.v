(** Real-line diameter estimates supporting Federer (1969), 2.10.7, pp.
    174–175, concluding that Hausdorff length equals Lebesgue measure on the
    line. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_segment_pair_distance]: supporting interval-diameter
    calculation for Federer 2.10.7, pp. 174–175 *)
Lemma real_segment_pair_distance (R : realType) (a b x y : R) :
  `[a,b] x -> `[a,b] y -> `|x-y|<=b-a.
Proof.
rewrite /= !in_itv /= => /andP[hax hxb] /andP[hay hyb].
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB; exact: lerB hyb hax.
- exact: lerB hxb hay.
Qed.

(** Source for [extended_metric_diameter_segment]: the diameter of the
    segment [a,b] is b-a, supporting Federer 2.10.7, pp. 174–175 Degenerate
    segments are included. *)
Lemma extended_metric_diameter_segment (R : realType) (a b : R) : a<=b ->
  @extended_metric_diameter R [the metricType R of real_line_metric R] `[a,b]=(b-a)%:E.
Proof.
move=> hab; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (metric_diameter_least (extended_metric_diameter_specification
    (X:=[the metricType R of real_line_metric R]) `[a,b])).
  + by rewrite lee_fin subr_ge0.
  + move=> x y hx hy; rewrite lee_fin real_line_metric_distanceE.
    exact: real_segment_pair_distance hx hy.
- have ha : `[a,b] a by rewrite /= in_itv /= lexx hab.
  have hb : `[a,b] b by rewrite /= in_itv /= lexx hab.
  have h := metric_diameter_upper (extended_metric_diameter_specification
    (X:=[the metricType R of real_line_metric R]) `[a,b]) hb ha.
  by rewrite real_line_metric_distanceE ger0_norm ?subr_ge0 in h.
Qed.

(** Source for [real_bounded_diameter_interval_hull]: supporting interval
    hull of a nonempty bounded subset in Federer 2.10.7, pp. 174–175. We use
    [inf A, inf A+d] when all pairwise distances are at most d; an attained
    infimum is not assumed. *)
Lemma real_bounded_diameter_interval_hull (R : realType) (A : set R) (d : R) :
  A !=set0 -> (forall x y, A x -> A y -> `|x-y|<=d) ->
  A `<=` `[inf A,inf A+d].
Proof.
move=> hA hd.
have hlow x : A x -> lbound A (x-d).
  move=> hx y hy.
  have h := le_trans (ler_norm (x-y)) (hd x y hx hy).
  move: h; rewrite !lerBlDr addrC; by [].
have hbounded : has_lbound A.
  have [x hx] := hA; exists (x-d); exact: hlow hx.
move=> x hx; rewrite /= in_itv /=; apply/andP; split.
- exact (ge_inf hbounded hx).
- rewrite -lerBlDr; exact (lb_le_inf hA (hlow x hx)).
Qed.
