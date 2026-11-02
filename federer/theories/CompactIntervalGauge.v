(** Federer (1969), 2.10.28, p. 191: the family F of nonempty compact real
    subintervals and the cost h(diam S), with empty-set cost zero. Specify
    intervals by their endpoint existence laws; no global endpoint choice is
    exposed. The cost uses the existing sealed diameter interface. Values on
    sets outside F and the empty set are an auxiliary total extension, not
    additional claims of the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype normed_module lra.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter MetricDiameterReal
  MetricDiameterMaps ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_real_interval]: direct
    nonempty compact interval family in 2.10.28,
    p. 191. Existence of ordered endpoints
    specifies membership; degenerate intervals remain
    included, as in the printed definition of F. *)
Definition is_compact_real_interval (R : realType) (A : set (real_line_metric R)) :=
  exists a b : R, a<=b /\ A=`[a,b].

(** Source for [compact_real_intervals]: direct
    family F in 2.10.28, p. 191,
    represented by the sets satisfying the
    abstract compact-interval predicate. *)
Definition compact_real_intervals (R : realType) : choiceType :=
  [the choiceType of set_type (@is_compact_real_interval R)].

(** Source for [concave_interval_cost]: direct
    zeta(S)=h(diam S) for intervals in
    2.10.28, p. 191. Taking the finite
    part of the existing abstract diameter
    gives a total auxiliary expression; subsequent
    interval calculations identify its finite value. *)
Definition concave_interval_cost (R : realType) (h : R -> R)
    (A : set (real_line_metric R)) : R :=
  h (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] A)).

(** Source for [compact_real_interval_nonempty]: supporting
    nonemptiness required in F in 2.10.28,
    p. 191, derived from its endpoint laws. *)
Lemma compact_real_interval_nonempty (R : realType) (A : set (real_line_metric R)) :
  is_compact_real_interval A -> A !=set0.
Proof. move=> [a [b [hab ->]]]; exists a; by rewrite /= in_itv /= lexx hab. Qed.

(** Source for [compact_real_interval_compact]: supporting
    compactness of the generators in 2.10.28,
    p. 191. Closed bounded intervals are
    general-topology background, also when degenerate. *)
Lemma compact_real_interval_compact (R : realType) (A : set (real_line_metric R)) :
  is_compact_real_interval A -> compact A.
Proof. move=> [a [b [_ ->]]]; exact: segment_compact. Qed.

(** Source for [compact_real_interval_closed]: supporting
    closed generators for the limit-set argument
    of 2.10.28(3), p. 192. *)
Lemma compact_real_interval_closed (R : realType) (A : set (real_line_metric R)) :
  is_compact_real_interval A -> closed A.
Proof.
move=> hA; exact: compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R])
  (compact_real_interval_compact hA).
Qed.

(** Source for [concave_interval_cost_segment]: direct
    cost identification h(b-a) for [a,b]
    in 2.10.28, pp. 191–193, including
    the zero-length interval. *)
Lemma concave_interval_cost_segment (R : realType) (h : R -> R) a b : a<=b ->
  concave_interval_cost h `[a,b]=h (b-a).
Proof. by move=> hab; rewrite /concave_interval_cost (extended_metric_diameter_segment hab). Qed.

(** Source for [concave_interval_cost_empty]: direct
    zeta(empty)=0 convention in 2.10.28,
    p. 191, obtained from h(0)=0 and
    the abstract empty-set diameter law. *)
Lemma concave_interval_cost_empty (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) : concave_interval_cost h set0=0.
Proof. by rewrite /concave_interval_cost extended_metric_diameter_empty; exact: interval_gauge_zero. Qed.

(** Source for [concave_interval_cost_nonnegative]: supporting
    nonnegative interval costs in 2.10.28,
    p. 191. The total auxiliary extension
    also remains nonnegative, since fine(+oo)=0. *)
Lemma concave_interval_cost_nonnegative (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) A : 0<=concave_interval_cost h A.
Proof.
rewrite /concave_interval_cost.
have hd := metric_diameter_nonnegative
  (extended_metric_diameter_specification (X:=[the metricType R of real_line_metric R]) A).
case hv : (@extended_metric_diameter R [the metricType R of real_line_metric R] A)=> [r| |] in hd *.
- have hr : 0<=r by move: hd; rewrite lee_fin.
  exact (@concave_interval_gauge_nonnegative R h hg r hr).
- rewrite (interval_gauge_zero hg); exact: lexx.
- by [].
Qed.

(** Source for [compact_real_interval_intersection]: supporting
    interval or empty intersections in the sum
    in 2.10.28(1), p. 191. Nonempty
    intersections stay in the printed family F. *)
Lemma compact_real_interval_intersection (R : realType) (A B : set (real_line_metric R)) :
  is_compact_real_interval A -> is_compact_real_interval B ->
  A `&` B !=set0 -> is_compact_real_interval (A `&` B).
Proof.
move=> [a [b [hab ->]]] [c [d [hcd ->]]] [x [hx hy]].
have /andP[hax hxb] : a<=x<=b by move: hx; rewrite /= in_itv.
have /andP[hcx hxd] : c<=x<=d by move: hy; rewrite /= in_itv.
exists (Order.max a c),(Order.min b d); split.
- have hl : Order.max a c<=x by rewrite ge_max hax hcx.
  have hu : x<=Order.min b d by rewrite le_min hxb hxd.
  exact: le_trans hl hu.
- apply/seteqP; split=> y.
  + move=> [hy1 hy2]; move: hy1 hy2; rewrite /= !in_itv /= => /andP[hay hyb] /andP[hcy hyd].
    by rewrite ge_max le_min hay hcy hyb hyd.
  + rewrite /= in_itv /= ge_max le_min=> /andP [/andP[hay hcy] /andP[hyb hyd]].
    split; by rewrite /= in_itv /= ?hay ?hyb ?hcy ?hyd.
Qed.

(** Source for [concave_interval_cost_subset]: supporting monotonicity used
    to shrink the test interval in the proof of 2.10.28(1), p. 192 *)
Lemma concave_interval_cost_subset (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) A B :
  is_compact_real_interval A -> is_compact_real_interval B -> A `<=` B ->
  concave_interval_cost h A<=concave_interval_cost h B.
Proof.
move=> [a [b [hab ->]]] [c [d [hcd ->]]] hsub.
have ha : `[a,b] a by rewrite /= in_itv /= lexx hab.
have hb : `[a,b] b by rewrite /= in_itv /= lexx hab.
have /andP[hca had] : c<=a<=d by move: (hsub a ha); rewrite /= in_itv.
have /andP[hcb hbd] : c<=b<=d by move: (hsub b hb); rewrite /= in_itv.
rewrite !concave_interval_cost_segment //.
apply: (@interval_gauge_increasing R h hg (b-a) (d-c)); lra.
Qed.
