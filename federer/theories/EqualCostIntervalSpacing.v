(** Federer (1969), 2.10.28(4), p. 192, and its use in 2.10.29, p. 194: the
    spacing of Phi(J,n) is determined by the parent interval and its
    equal-cost radius. Relate arbitrary endpoint descriptions to an already
    specified common radius and spacing, without choosing or exposing a
    family witness. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP EqualCostIntervalClipped.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_interval_split_spacing_unique]: supporting
    independence of endpoints and radius witnesses
    for the spacing in 2.10.28(4), p. 192.
    The actual parent diameter fixes the radius
    by strict gauge growth, hence fixes t. *)
Lemma compact_interval_split_spacing_unique (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) n (r tau : R) :
  is_cantor_split_radius h
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n r ->
  tau=cantor_split_spacing
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n r ->
  forall a b s t : R, val J=(`[a,b] : set (real_line_metric R)) ->
    is_cantor_split_radius h (b-a) n s -> t=cantor_split_spacing (b-a) n s -> t=tau.
Proof.
move=> hr htau a b s t hJ hs ht.
have [x hx] := compact_real_interval_nonempty (set_valP J).
have /andP[hax hxb] : a<=x<=b by move: hx; rewrite hJ /= in_itv.
have hab : a<=b := le_trans hax hxb.
have hdiam : fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))=b-a.
  by rewrite hJ (extended_metric_diameter_segment hab).
rewrite hdiam in hr htau.
have he := @cantor_split_radius_unique R h hg (b-a) n s r hs hr.
by rewrite ht he -htau.
Qed.

(** Source for [equal_cost_interval_clipped_at_spacing]: direct
    constant-three estimate of 2.10.28(4), p. 192,
    stated at an already specified common spacing.
    This supporting form is used at the
    uniform parent scales in 2.10.29, p. 194;
    it adds no alternative endpoint assumptions. *)
Theorem equal_cost_interval_clipped_at_spacing (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J T : compact_real_intervals R) n F (r tau : R) :
  is_equal_cost_interval_family h J n F ->
  is_cantor_split_radius h
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n r ->
  tau=cantor_split_spacing
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n r ->
  tau<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)) ->
  \sum_(S <- F) concave_interval_cost h (val T `&` val S)<=
    3*concave_interval_cost h (val J)*
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
Proof.
move=> hPhi hr htau hlarge; apply: (@federer_2_10_28_4_clipped R h hg J T n F hPhi).
move=> a b s t hJ hs ht.
by rewrite (@compact_interval_split_spacing_unique R h hg J n r tau hr htau a b s t hJ hs ht).
Qed.
