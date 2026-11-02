(** Federer (1969), 2.10.28(3), p. 192: both limit-mass conclusions for a
    tree of special interval families. Preserve the single-root correction
    in Federer's erratum p. 4, book p. 192 line 4. The upper bound follows
    from fine level covers; the lower bound on each member follows from
    compact finite open covers and cost conservation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP ConcaveIntervalMeasure
  SpecialIntervalFamilyUP SpecialIntervalTreeUpperBound SpecialIntervalTreeLowerBound SpecialIntervalLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_28_3]: direct two
    measure conclusions in 2.10.28(3),
    p. 192, with card(H_0)=1 from
    erratum p. 4, book p. 192 line 4.
    Every compact test interval has the
    upper bound, and each member of each
    level has exact mass. Empty limits,
    zero-cost members and dead singleton
    branches remain included. *)
Theorem federer_2_10_28_3 (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) (A : set (real_line_metric R))
    (hA : is_special_interval_tree_limit H A) :
  (forall T : compact_real_intervals R,
    concave_interval_measure h (A `&` val T)<=(concave_interval_cost h (val T))%:E) /\
  (forall j T, T \in H j ->
    concave_interval_measure h (A `&` val T)=(concave_interval_cost h (val T))%:E).
Proof.
split; first exact: (@federer_2_10_28_3_upper R h hg H ht A hA).
move=> j T hT; apply/eqP; rewrite eq_le.
by rewrite (@federer_2_10_28_3_upper R h hg H ht A hA T)
  (@federer_2_10_28_3_lower R h hg H ht A hA j T hT).
Qed.

(** Source for [federer_2_10_28_3_selected_limit]: direct
    same conclusions of 2.10.28(3), p. 192,
    for the public opaque limit set. Its
    construction stays hidden; apply only the
    proved membership specification. *)
Theorem federer_2_10_28_3_selected_limit (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) :
  (forall T : compact_real_intervals R,
    concave_interval_measure h (special_interval_tree_limit H `&` val T)<=
      (concave_interval_cost h (val T))%:E) /\
  (forall j T, T \in H j ->
    concave_interval_measure h (special_interval_tree_limit H `&` val T)=(concave_interval_cost h (val T))%:E).
Proof.
exact: (@federer_2_10_28_3 R h hg H ht _ (@special_interval_tree_limit_specification R H)).
Qed.
