(** Federer (1969), 2.10.29, p. 194: derive the factor-six linear mass bound
    for a test interval whose length lies between the next spacing and the
    current common parent width. It meets at most two parents;
    2.10.28(3)–(4) contributes a factor three within each. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge CompactIntervalDiameter
  ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws ConcaveIntervalMeasure SpecialIntervalFamilyUP
  CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP EqualWidthIntervalPacking
  SpecialIntervalLimitLocalBounds MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_uniform_linear_mass_bound]: direct
    factor-six upper bound used in both
    cases of 2.10.29, p. 194. State
    the estimate for an arbitrary concave
    gauge h; the book applies h(r)=c*r^m.
    Uniform parent widths and actual child
    Phi laws are hypotheses; the mass
    bound is proved, not assumed. *)
Theorem special_interval_uniform_linear_mass_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) H (ht : is_special_interval_tree h H)
    A (hA : is_special_interval_tree_limit H A) j n (r s tau : R) (T : compact_real_intervals R) :
  0<r ->
  (forall J, J \in H j -> fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))=r) ->
  (forall J, J \in H j -> is_equal_cost_interval_family h J n
    (special_interval_restriction (H j.+1) (val J))) ->
  is_cantor_split_radius h r n s -> tau=cantor_split_spacing r n s ->
  tau<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)) ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))<=r ->
  (concave_interval_measure h (A `&` val T)<=
    (6*h r*fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/r)%:E)%E.
Proof.
move=> hr hwidth hPhi hs htau hlarge hsmall.
pose I := compact_real_intervals R.
pose d := fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)).
pose G := [fset J in H j | `[< val T `&` val J !=set0 >]].
pose K := 3*h r*d/r.
have hd : 0<=d := @compact_interval_diameter_nonnegative R (val T) (set_valP T).
have hhr : 0<=h r := @concave_interval_gauge_nonnegative R h hg r (ltW hr).
have hK : 0<=K.
  rewrite /K; apply: mulr_ge0; last by rewrite invr_ge0; exact: ltW hr.
  apply: mulr_ge0=> //; apply: mulr_ge0=> //; exact: ler0n.
have hcard : (#|` G|<=2)%N.
  exact (@equal_width_interval_meeting_count R (H j) T r hr hwidth
    (fun S U hS hU hne=>@special_tree_disjoint R h H ht j S U hS hU hne) hsmall).
have hcardR : ((#|` G|)%:R<=2 :> R) by rewrite ler_nat.
have hparent (J : I) : J \in G ->
    (concave_interval_measure h ((A `&` val T) `&` val J)<=K%:E)%E.
  rewrite /G in_fset /= => /andP[hJ hactive].
  have hJwidth := hwidth J hJ.
  have hsplit : is_cantor_split_radius h
      (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n s by rewrite hJwidth.
  have hspace : tau=cantor_split_spacing
      (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n s by rewrite hJwidth.
  have hh := @special_interval_limit_parent_phi_bound R h hg H ht A hA j J T n s tau
    hJ (hPhi J hJ) hsplit hspace hlarge.
  by rewrite /concave_interval_cost hJwidth in hh.
have hcover : A `&` val T `<=` \bigcup_(J in [set J : I | J \in G]) ((A `&` val T) `&` val J).
  move=> x [hxA hxT]; have [J [hJ hxJ]] := (hA x).1 hxA j.
  exists J; last by split; [split |].
  change (is_true (J \in G)).
  rewrite /G in_fset /=; apply/andP; split=> //; apply/asboolP; exists x; by split.
have hm := concave_interval_measure_is_measure hg.
have hh := @measure_indexed_cover R (real_line_metric R) I (concave_interval_measure h) hm
  (A `&` val T) [set J | J \in G] (fun J=>(A `&` val T) `&` val J)
  (finite_set_countable (finite_fset G)) hcover.
rewrite (@nonnegative_sum_finite R I G (fun J=>concave_interval_measure h ((A `&` val T) `&` val J))
  (fun J _=>measure_nonnegative hm _)) in hh.
have hparts : (\sum_(J <- G) concave_interval_measure h ((A `&` val T) `&` val J)<=
    (\sum_(J <- G) K)%:E)%E.
  rewrite -sumEFin !big_seq; apply: lee_sum=> J hJ; exact: hparent J hJ.
have hsum : (\sum_(J <- G) K)=(#|` G|)%:R*K.
  by rewrite big_seq_fsetE /= sumr_const -cardfE [RHS]mulr_natl.
have hfinal : ((\sum_(J <- G) K)%:E<=(6*h r*d/r)%:E)%E.
  rewrite hsum lee_fin; apply: le_trans (ler_wpM2r hK hcardR) _.
  rewrite /K; lra.
exact: le_trans hh (le_trans hparts hfinal).
Qed.
