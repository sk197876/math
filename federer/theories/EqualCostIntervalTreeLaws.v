(** Federer (1969), 2.10.28, p. 193: the equal-cost recursion gives special,
    disjoint levels, with positive-length members and geometrically
    shrinking mesh. Derive these from the recursion laws, without accessing
    its implementation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge
  ConcaveIntervalGaugeUP EqualCostIntervalFamilyUP EqualCostIntervalMesh EqualCostIntervalSpecial
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP SpecialIntervalFamilyBasic
  SpecialIntervalRefinement SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_tree_level_special]: supporting
    specialness of every H_j for the root
    in 2.10.28, p. 193, by induction
    using (2) and (4). *)
Theorem equal_cost_tree_level_special (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H
    (ht : is_equal_cost_interval_tree h J n H) :
  forall j, is_special_interval_family h J (H j).
Proof.
elim=> [|j ih].
- rewrite (equal_cost_tree_root ht); exact: (@special_interval_singleton R h hg J).
- have [K [hK he]] := equal_cost_tree_step ht j.
  rewrite he; apply: (@federer_2_10_28_2 R h hg J (H j) K ih)=> S hS.
  exact: (@federer_2_10_28_4_special R h hg S (n j) (K S) (hK S hS)).
Qed.

(** Source for [equal_cost_tree_member_positive]: supporting
    positivity of all interval lengths in the
    recursion, 2.10.28, p. 193. Every
    current parent admits its specified positive
    child family. No positivity is imposed as
    an extra law of the recursive witness. *)
Lemma equal_cost_tree_member_positive (R : realType) (h : R -> R) J n H
    (ht : is_equal_cost_interval_tree h J n H) j S : S \in H j ->
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)).
Proof.
move=> hS; have [K [hK _]] := equal_cost_tree_step ht j.
exact: equal_cost_interval_parent_nondegenerate (hK S hS).
Qed.

(** Source for [equal_cost_tree_mesh_bound]: supporting
    diam(S)<=diam(J)*2^-j for S in H_j
    in the construction of 2.10.28, p. 193.
    The book requires n_j>=2; the strict
    child bound in (4) yields this uniform
    weak bound, including level zero. *)
Theorem equal_cost_tree_mesh_bound (R : realType) (h : R -> R) J n H
    (ht : is_equal_cost_interval_tree h J n H) : forall j S, S \in H j ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))<=
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))*(2^-1)^+j.
Proof.
elim=> [S|j ih S].
- rewrite (equal_cost_tree_root ht) in_fset1=> /eqP ->; by rewrite expr0 mulr1.
- have [K [hK he]] := equal_cost_tree_step ht j.
  rewrite he=> /special_interval_refinement_membership[T [hT hS]].
  have hPhi := hK T hT.
  have [hpos hshrink] := @equal_cost_interval_child_mesh R h T (n j) (K T) S hPhi hS.
  have hn := hPhi.1.
  have hNR : (2<=((n j)%:R) :> R) by rewrite ler_nat.
  have hN0 : (0<((n j)%:R) :> R) by lra.
  have hTpos := @equal_cost_tree_member_positive R h J n H ht j T hT.
  have hh : fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/(n j)%:R<=
      fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))/2.
    have htwo : (0<2 :> R) by lra.
    have hv : (((n j)%:R)^-1<=2^-1 :> R).
      by rewrite (@lef_pV2 R (n j)%:R 2 hN0 htwo).
    exact (ler_wpM2l (ltW hTpos) hv).
  have hhalf0 : (0<=2^-1 :> R) by rewrite invr_ge0 ler0n.
  have hmul := ler_wpM2r hhalf0 (ih T hT).
  rewrite exprSr mulrA; exact (le_trans (ltW hshrink) (le_trans hh hmul)).
Qed.
