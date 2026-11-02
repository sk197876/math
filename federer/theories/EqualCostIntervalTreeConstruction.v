(** Federer (1969), 2.10.28, p. 193: existence of the recursively refined
    interval levels. The recursion is private; its public content is the
    root and refinement laws. The auxiliary total child selector uses an
    empty value on degenerate parents, which never occur in the resulting
    tree. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge
  ConcaveIntervalGaugeUP EqualCostIntervalFamilyUP EqualCostIntervalFamily
  EqualCostIntervalMesh EqualCostIntervalTreeUP SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_tree_total_children]: private
    total selector supporting the recursion in
    2.10.28, p. 193. Only its positive-parent
    branch will be used in the existence proof;
    the empty fallback is not a proposed
    definition of Phi for point intervals. *)
Definition equal_cost_tree_total_children (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) n (hn : (2<=n)%N) (S : compact_real_intervals R) :=
  if pselect (0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)))
  is left hS then @equal_cost_interval_family R h hg S n hS hn else fset0.

(** Source for [equal_cost_tree_total_children_laws]: supporting
    agreement with Phi(S,n) on every actual
    positive-length parent, 2.10.28, p. 193.
    The proof uses the sealed family laws. *)
Lemma equal_cost_tree_total_children_laws (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) n (hn : (2<=n)%N) (S : compact_real_intervals R) :
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)) ->
  is_equal_cost_interval_family h S n (@equal_cost_tree_total_children R h hg n hn S).
Proof.
move=> hS; rewrite /equal_cost_tree_total_children; case: pselect=> [hp|hnp]; last by exfalso; exact: hnp.
exact: equal_cost_interval_family_specification.
Qed.

(** Source for [equal_cost_tree_recursive_levels]: private
    recursive existence witness for H_j in
    2.10.28, p. 193. The exposed interface
    will retain only its abstract recurrence laws. *)
Fixpoint equal_cost_tree_recursive_levels (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R)
    (n : nat -> nat) (hn : forall j, (2<=n j)%N) (j : nat) :=
  if j is k.+1 then special_interval_refinement
    (@equal_cost_tree_recursive_levels R h hg J n hn k)
    (@equal_cost_tree_total_children R h hg (n k) (hn k)) else [fset J].

(** Source for [equal_cost_tree_recursive_positive]: supporting
    nondegeneracy invariant of the existence
    recursion, 2.10.28, p. 193. The
    positive child lengths in (4) prevent
    the selector's degenerate branch from occurring. *)
Lemma equal_cost_tree_recursive_positive (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R)
    (n : nat -> nat) (hn : forall j, (2<=n j)%N)
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J))) :
  forall j S, S \in @equal_cost_tree_recursive_levels R h hg J n hn j ->
    0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)).
Proof.
elim=> [S|j ih S]; first by rewrite /= in_fset1=> /eqP ->.
change (S \in special_interval_refinement (@equal_cost_tree_recursive_levels R h hg J n hn j)
  (@equal_cost_tree_total_children R h hg (n j) (hn j)) ->
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))).
move=> /special_interval_refinement_membership[T [hT hS]].
have hPhi := @equal_cost_tree_total_children_laws R h hg (n j) (hn j) T (ih T hT).
exact: (@equal_cost_interval_child_mesh R h T (n j) _ S hPhi hS).1.
Qed.

(** Source for [equal_cost_interval_tree_exists]: direct
    existence of the recursion used to define
    A(m,n) in 2.10.28, p. 193, before
    imposing a particular power gauge. The
    same recursion works for every admitted
    concave gauge and nondegenerate initial interval. *)
Theorem equal_cost_interval_tree_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R)
    (n : nat -> nat)
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : forall j, (2<=n j)%N) : exists H, is_equal_cost_interval_tree h J n H.
Proof.
exists (@equal_cost_tree_recursive_levels R h hg J n hn); constructor; first by [].
move=> j; exists (@equal_cost_tree_total_children R h hg (n j) (hn j)); split; last by [].
move=> S hS; apply: equal_cost_tree_total_children_laws.
exact: (@equal_cost_tree_recursive_positive R h hg J n hn hJ j S hS).
Qed.
