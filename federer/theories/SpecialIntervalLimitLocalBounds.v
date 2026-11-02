(** Federer (1969), 2.10.29, p. 194: use 2.10.28(3)–(4), pp. 192–193, inside
    one parent interval to bound the limit mass in a test interval by the
    clipped cost of its children, then by
    3*zeta(parent)*diam(test)/diam(parent). Preserve empty and point
    intersections. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  ConcaveIntervalMeasure SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalTreeLevels
  SpecialIntervalTreeUpperBound CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP EqualCostIntervalSpacing
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [special_interval_limit_parent_child_cover]: supporting
    cover of A intersect a parent by its
    next-level child intervals in the use of
    2.10.28(3) in 2.10.29, p. 194.
    A child meeting a given parent cannot
    lie under a different disjoint parent. *)
Lemma special_interval_limit_parent_child_cover (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H)
    A (hA : is_special_interval_tree_limit H A) j (J : compact_real_intervals R) :
  J \in H j -> A `&` val J `<=`
    \bigcup_(S in [set S | S \in special_interval_restriction (H j.+1) (val J)]) val S.
Proof.
move=> hJ x [hxA hxJ]; have [S [hS hxS]] := (hA x).1 hxA j.+1.
have hSlater : S \in H (j+1)%N by rewrite addn1.
have [hSJ|hdis] := @special_interval_tree_level_relation R h H ht j 1%N J S hJ hSlater.
- exists S; last exact hxS.
  apply/special_interval_restriction_membership; by split.
- have hmem : (val S `&` val J) x by split.
  by rewrite hdis in hmem.
Qed.

(** Source for [special_interval_limit_clipped_mass_bound]: supporting
    psi(A intersect T intersect S)<=zeta(T intersect S)
    from 2.10.28(3), p. 192, used in
    2.10.29, p. 194. An empty intersection
    has both zero mass and zero cost, so
    no nonempty-intersection hypothesis is added. *)
Lemma special_interval_limit_clipped_mass_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) H (ht : is_special_interval_tree h H)
    A (hA : is_special_interval_tree_limit H A) (T S : compact_real_intervals R) :
  concave_interval_measure h (A `&` (val T `&` val S))<=
    (concave_interval_cost h (val T `&` val S))%:E.
Proof.
case: (pselect (val T `&` val S !=set0))=> hnon.
- have hI := compact_real_interval_intersection (set_valP T) (set_valP S) hnon.
  pose U : compact_real_intervals R := Sub (val T `&` val S) (mem_set hI).
  exact (@federer_2_10_28_3_upper R h hg H ht A hA U).
- have he : val T `&` val S=set0.
    apply/seteqP; split=> [x hx|x []]; apply: hnon; by exists x.
  by rewrite he setI0 (measure_empty (concave_interval_measure_is_measure hg))
    (concave_interval_cost_empty hg).
Qed.

(** Source for [special_interval_limit_finite_clipped_cover]: supporting
    clipped child-cost upper bound in the
    application of 2.10.28(3)–(4) within
    2.10.29, p. 194. The cover is
    indexed by its finite child family, so
    coincident clipped sets keep their multiplicity. *)
Lemma special_interval_limit_finite_clipped_cover (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) H (ht : is_special_interval_tree h H)
    A (hA : is_special_interval_tree_limit H A) (T J : compact_real_intervals R)
    (F : {fset compact_real_intervals R}) :
  A `&` val J `<=` \bigcup_(S in [set S | S \in F]) val S ->
  concave_interval_measure h ((A `&` val T) `&` val J)<=
    (\sum_(S <- F) concave_interval_cost h (val T `&` val S))%:E.
Proof.
move=> hcover.
have hm := concave_interval_measure_is_measure hg.
have hc : (A `&` val T) `&` val J `<=`
    \bigcup_(S in [set S | S \in F]) (A `&` (val T `&` val S)).
  move=> x [[hxA hxT] hxJ]; have [S hS hxS] := hcover x (conj hxA hxJ).
  exists S=> //; by split=> //; split.
have hh := @measure_indexed_cover R (real_line_metric R) (compact_real_intervals R)
  (concave_interval_measure h) hm ((A `&` val T) `&` val J) [set S | S \in F]
  (fun S=>A `&` (val T `&` val S)) (finite_set_countable (finite_fset F)) hc.
rewrite (@nonnegative_sum_finite R (compact_real_intervals R) F
  (fun S=>concave_interval_measure h (A `&` (val T `&` val S)))
  (fun S _=>measure_nonnegative hm _)) in hh.
apply: le_trans hh _; rewrite -sumEFin; apply: lee_sum=> S _.
exact (@special_interval_limit_clipped_mass_bound R h hg H ht A hA T S).
Qed.

(** Source for [special_interval_limit_parent_phi_bound]: direct
    one-parent constant-three mass estimate from
    2.10.28(3)–(4) used in 2.10.29,
    p. 194. The test interval is at
    least as long as the specified spacing;
    the child family is exactly the parent's
    next-level restriction. *)
Theorem special_interval_limit_parent_phi_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) H (ht : is_special_interval_tree h H)
    A (hA : is_special_interval_tree_limit H A) j (J T : compact_real_intervals R) n (r tau : R) :
  J \in H j ->
  is_equal_cost_interval_family h J n (special_interval_restriction (H j.+1) (val J)) ->
  is_cantor_split_radius h
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n r ->
  tau=cantor_split_spacing
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) n r ->
  (tau<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)))%R ->
  concave_interval_measure h ((A `&` val T) `&` val J)<=
    (3*concave_interval_cost h (val J)*
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))%R%:E.
Proof.
move=> hJ hPhi hr htau hlarge.
have hmass := @special_interval_limit_finite_clipped_cover R h hg H ht A hA T J _
  (@special_interval_limit_parent_child_cover R h H ht A hA j J hJ).
have hclip := @equal_cost_interval_clipped_at_spacing R h hg J T n _ r tau hPhi hr htau hlarge.
apply: le_trans hmass _; by rewrite lee_fin.
Qed.
