(** Federer (1969), 2.10.28(4), pp. 192–193: the additional constant-three
    clipped estimate. The proof counts the first and last intersected child
    indices rather than choosing a floor k. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  CompactIntervalGaugeGeometry ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws
  CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP EqualCostIntervalEnumeration
  EqualSpacingClippedCount IntervalClipLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_28_4_clipped]: direct
    sum zeta(T intersect S)<=3*zeta(J)*diam(T)/diam(J)
    for diam(T)>=t in 2.10.28(4), p. 192,
    proof p. 193. The spacing condition is
    expressed for the parameters in the abstract
    family laws; no implementation is exposed. *)
Theorem federer_2_10_28_4_clipped (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J T : compact_real_intervals R) n F :
  is_equal_cost_interval_family h J n F ->
  (forall a b s t : R, val J=(`[a,b] : set (real_line_metric R)) ->
    is_cantor_split_radius h (b-a) n s -> t=cantor_split_spacing (b-a) n s ->
    t<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))) ->
  \sum_(S <- F) concave_interval_cost h (val T `&` val S)<=
    3*concave_interval_cost h (val J)*
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
Proof.
move=> hPhi hlarge.
have [hn [a [b [s [t [f [hJ [hd [hs [ht [hvalue [hf hF]]]]]]]]]]]] :=
  equal_cost_interval_ordinal_enumeration hPhi.
have [u [v [huv hT]]] := set_valP T.
have hab : a<=b by lra.
have hspos := (cantor_split_radius_bounds hs).1.
have hst : s<t by rewrite ht; exact: cantor_split_spacing_strict hn hs.
have hL : t<=v-u.
  have hh := hlarge a b s t hJ hs ht.
  by rewrite hT (extended_metric_diameter_segment huv) in hh.
have hend : b-a=(n%:R-1)*t+s by rewrite ht cantor_split_last_endpoint.
have hN : (0<n%:R :> R) by rewrite ltr0n; exact: leq_trans (leqnSn 1%N) hn.
have hhs := cantor_split_radius_cost hs.
pose P (i : 'I_n) := (a+i%:R*t<=v) && (u<=a+i%:R*t+s).
have hbound : (\sum_(i : 'I_n) h (real_interval_clip_length u v (a+i%:R*t) (a+i%:R*t+s)))<=
    (#|P|)%:R*h s.
  have hsum : (#|P|)%:R*h s=\sum_(i : 'I_n) if P i then h s else 0.
    by rewrite mulr_natl -sumr_const big_mkcond.
  rewrite hsum.
  apply: ler_sum=> i _; exact: (@equal_spacing_clipped_cost_bound R h hg a s t u v i%:R (ltW hspos)).
have hcount := @equal_spacing_intersected_count_bound R n a s t u v hspos hst hL.
have hdNt : b-a<=n%:R*t by lra.
have hc := @concave_interval_gauge_nonnegative R h hg (b-a) (ltW hd).
have hratio := @equal_spacing_count_cost_ratio R (#|P|)%:R (b-a) n%:R t (v-u) (h (b-a))
  (@ler0n R (#|P|)) hd hN hc hdNt hcount.
rewrite hJ hT (concave_interval_cost_segment h hab)
  (extended_metric_diameter_segment huv) (extended_metric_diameter_segment hab) hF big_imfset /=; last first.
  by move=> i j hi hj; exact: hf.
rewrite undup_id ?enum_uniq // big_enum.
have he : (\sum_(i : 'I_n) concave_interval_cost h ((`[u,v] : set (real_line_metric R)) `&` val (f i)))=
    \sum_(i : 'I_n) h (real_interval_clip_length u v (a+i%:R*t) (a+i%:R*t+s)).
  apply: eq_bigr=> i _; by rewrite hvalue (concave_interval_intersection_cost hg).
rewrite he; apply: le_trans hbound _; by rewrite hhs.
Qed.
