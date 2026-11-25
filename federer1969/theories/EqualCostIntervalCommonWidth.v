(** Federer (1969), 2.10.29, p. 193: all intervals at a fixed Cantor level
    have the same length. Prove this directly from the abstract tree laws,
    without choosing a scalar width sequence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  CantorSplitRadiusUP EqualCostIntervalChildLaws EqualCostIntervalTreeUP SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_tree_same_level_width]: direct
    same-level equal lengths in 2.10.29,
    p. 193. Parent width equality and uniqueness
    of equal-cost child radii suffice. *)
Theorem equal_cost_interval_tree_same_level_width (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H
    (ht : is_equal_cost_interval_tree h J n H) :
  forall j S T, S \in H j -> T \in H j ->
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T)).
Proof.
elim=> [S T|j ih S T].
- rewrite (equal_cost_tree_root ht) !in_fset1=> /eqP -> /eqP ->; by [].
- move=> hS hT; have [K [hK he]] := equal_cost_tree_step ht j.
  rewrite he in hS hT.
  have [U [hU hSU]] := (@special_interval_refinement_membership R (H j) K S).1 hS.
  have [V [hV hTV]] := (@special_interval_refinement_membership R (H j) K T).1 hT.
  have hs := @equal_cost_interval_child_split_laws R h U (n j) (K U) S (hK U hU) hSU.
  have htau := @equal_cost_interval_child_split_laws R h V (n j) (K V) T (hK V hV) hTV.
  rewrite (ih U V hU hV) in hs.
  exact (@cantor_split_radius_unique R h hg _ (n j) _ _ hs htau).
Qed.
