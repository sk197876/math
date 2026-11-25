(** Federer (1969), 2.10.28, p. 193: the Phi recursion and (3) produce a
    compact limit of exactly the root's gauge cost. First prove this for
    every admissible concave gauge and nondegenerate root, before the
    power-gauge instance A(m,n). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge
  ConcaveIntervalGaugeUP ConcaveIntervalMeasure EqualCostIntervalTreeUP EqualCostIntervalTree
  EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP SpecialIntervalLimitLaws
  SpecialIntervalLimit SpecialIntervalTreeMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [equal_cost_interval_limit_root_subset]: supporting
    containment of A(m,n) in its initial
    interval I in 2.10.28, p. 193.
    This follows from the root and limit
    membership laws and requires no cost formula. *)
Lemma equal_cost_interval_limit_root_subset (R : realType) (h : R -> R) J n H A :
  is_equal_cost_interval_tree h J n H -> is_special_interval_tree_limit H A -> A `<=` val J.
Proof.
move=> ht hA x hx; have [S [hS hxS]] := (hA x).1 hx 0%N.
move: hS; rewrite (equal_cost_tree_root ht) in_fset1=> /eqP hSJ; by rewrite -hSJ.
Qed.

(** Source for [equal_cost_interval_limit_mass]: direct
    exact limit mass obtained in 2.10.28,
    p. 193, before specialising h to the
    normalised power gauge. Also retain the
    arbitrary test-interval bound needed for f. *)
Theorem equal_cost_interval_limit_mass (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H A :
  is_equal_cost_interval_tree h J n H -> is_special_interval_tree_limit H A ->
  compact A /\ A `<=` val J /\
  concave_interval_measure h A=(concave_interval_cost h (val J))%:E /\
  forall T : compact_real_intervals R,
    concave_interval_measure h (A `&` val T)<=(concave_interval_cost h (val T))%:E.
Proof.
move=> ht hA.
have hspecial := @equal_cost_interval_tree_special R h hg J n H ht.
have [hupper hexact] := @federer_2_10_28_3 R h hg H hspecial A hA.
have hsub := @equal_cost_interval_limit_root_subset R h J n H A ht hA.
have hroot : J \in H 0%N by rewrite (equal_cost_tree_root ht) in_fset1.
have he : A `&` val J=A.
  apply/seteqP; split=> x hx; first exact hx.1.
  by split; [exact hx | exact: hsub x hx].
split; first exact: interval_tree_limit_compact hA.
split=> //; split=> //; by move: (hexact 0%N J hroot); rewrite he.
Qed.

(** Source for [equal_cost_cantor_set]: direct limit
    of the prescribed Phi recursion in 2.10.28,
    p. 193, generalised to the stated gauge
    and initial interval. Both recursive levels
    and their limit are exposed only through
    their previously proved opaque interfaces. *)
Definition equal_cost_cantor_set (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) (n : nat -> nat)
    (hJ : (0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))%R)
    (hn : forall j, (2<=n j)%N) :=
  special_interval_tree_limit (@equal_cost_interval_tree R h hg J n hJ hn).

(** Source for [equal_cost_cantor_set_mass]: direct
    exact mass and interval bound for the
    chosen compact limit in 2.10.28, p. 193.
    The general-gauge statement does not assert
    Lebesgue nullity, which needs a power gauge
    of exponent strictly between zero and one. *)
Theorem equal_cost_cantor_set_mass (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) (n : nat -> nat)
    (hJ : (0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))%R)
    (hn : forall j, (2<=n j)%N) :
  let A := @equal_cost_cantor_set R h hg J n hJ hn in
  compact A /\ A `<=` val J /\
  concave_interval_measure h A=(concave_interval_cost h (val J))%:E /\
  forall T : compact_real_intervals R,
    concave_interval_measure h (A `&` val T)<=(concave_interval_cost h (val T))%:E.
Proof.
apply: (@equal_cost_interval_limit_mass R h hg J n _ _
  (@equal_cost_interval_tree_specification R h hg J n hJ hn)).
exact: special_interval_tree_limit_specification.
Qed.
