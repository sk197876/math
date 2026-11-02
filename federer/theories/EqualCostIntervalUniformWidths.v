(** Federer (1969), 2.10.29, p. 193: the interval diameters at each fixed
    Cantor level are equal. Derive this from the abstract equal-cost family
    and recursion laws, with the scalar width sequence specified by its
    split laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  CantorSplitRadiusUP EqualCostIntervalChildLaws EqualCostIntervalTreeUP SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_tree_uniform_widths]: direct
    equality of all interval lengths at a
    fixed level of 2.10.29, p. 193.
    Its abstract scalar sequence has the root
    length and the same equal-cost split laws;
    uniqueness of each radius proves equality. *)
Theorem equal_cost_interval_tree_uniform_widths (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H (q : nat -> R) :
  is_equal_cost_interval_tree h J n H ->
  q 0%N=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) ->
  (forall j, is_cantor_split_radius h (q j) (n j) (q j.+1)) ->
  forall j S, S \in H j ->
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=q j.
Proof.
move=> ht hroot hq; elim=> [S|j ih S].
- rewrite (equal_cost_tree_root ht) in_fset1=> /eqP ->; exact: esym hroot.
- have [K [hK he]] := equal_cost_tree_step ht j.
  rewrite he=> /special_interval_refinement_membership[T [hT hS]].
  have hchild := @equal_cost_interval_child_split_laws R h T (n j) (K T) S (hK T hT) hS.
  rewrite (ih T hT) in hchild.
  exact: (@cantor_split_radius_unique R h hg (q j) (n j) _ _ hchild (hq j)).
Qed.
