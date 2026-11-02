(** Federer (1969), 2.10.28, p. 193: abstract laws of A(m,n) and its
    cumulative function f. Use an arbitrary positive normalising constant c
    in h(t)=c*t^m. The book's choice is alpha(m)*2^-m; identifying that
    real-degree normalisation remains a separate dependency. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge RealPower ConcaveIntervalMeasure
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP MeasureRestriction FiniteCumulativeFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_power_cantor_pair]: direct
    root [0,1], Phi recursion, intersection limit
    and cumulative-value equation in 2.10.28,
    p. 193, with the explicit coefficient c.
    Compactness, exact mass, Holder continuity,
    range, nullity and differentiation conclusions
    are consequences, not defining assumptions. *)
Definition is_power_cantor_pair (R : realType) (c m : R) (n : nat -> nat)
    (A : set (real_line_metric R)) (f : R -> R) :=
  exists (J : compact_real_intervals R) (H : nat -> {fset compact_real_intervals R}),
    val J=(`[0,1] : set (real_line_metric R)) /\
    is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H /\
    is_special_interval_tree_limit H A /\
    is_finite_cumulative_function (measure_restrict (concave_interval_measure (fun t=>c*real_power t m)) A) f.
