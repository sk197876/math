(** Federer (1969), 2.10.28(4), p. 192: public Phi(J,n) and its abstract
    laws. The finite-image construction remains hidden. All later estimates
    must follow from the specified family and concave-gauge laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter ConcaveIntervalGaugeUP
  EqualCostIntervalFamilyUP EqualCostIntervalFamilySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_family]: direct
    Phi(J,n) in 2.10.28(4), p. 192,
    through its opaque specification. *)
Definition equal_cost_interval_family (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) n
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : (2<=n)%N) := @EqualCostIntervalFamily.value R h hg J n hJ hn.

(** Source for [equal_cost_interval_family_specification]: direct
    interval, radius and spacing laws of
    Phi(J,n), 2.10.28(4), p. 192. *)
Lemma equal_cost_interval_family_specification (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (J : compact_real_intervals R) n
    (hJ : 0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))
    (hn : (2<=n)%N) : is_equal_cost_interval_family h J n (@equal_cost_interval_family R h hg J n hJ hn).
Proof. exact: EqualCostIntervalFamily.laws. Qed.

(** Source for [equal_cost_interval_family_proof_independent]:
    supporting proof independence of Phi(J,n)
    in 2.10.28(4), p. 192. Uniqueness
    follows from the abstract family description
    and gauge laws, without computing its body. *)
Lemma equal_cost_interval_family_proof_independent (R : realType) (h : R -> R)
    (hg hg' : is_concave_interval_gauge h) (J : compact_real_intervals R) n hJ hJ' hn hn' :
  @equal_cost_interval_family R h hg J n hJ hn = @equal_cost_interval_family R h hg' J n hJ' hn'.
Proof.
exact: (@equal_cost_interval_family_unique R h hg J n _ _
  (@equal_cost_interval_family_specification R h hg J n hJ hn)
  (@equal_cost_interval_family_specification R h hg' J n hJ' hn')).
Qed.
