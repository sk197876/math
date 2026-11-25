(** Federer (1969), 2.10.28(3), p. 192: public limit-set interface. The set
    comprehension stays hidden; membership and compactness are exposed
    through the abstract laws. Source context and corrected tree hypotheses:
    SpecialIntervalFamilyUP.v. *)
(** Federer 2.10.28, pp. 192–193: source context and the abstract laws are
    recorded in the corresponding specification module. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  SpecialIntervalLimitLaws SpecialIntervalLimitSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [special_interval_tree_limit]: direct
    limit set A in 2.10.28(3), p. 192,
    through its proved opaque interface. *)
Definition special_interval_tree_limit (R : realType) (H : nat -> {fset compact_real_intervals R}) :=
  @SpecialIntervalLimit.value R H.

(** Source for [special_interval_tree_limit_specification]: direct
    membership laws for A in 2.10.28(3),
    p. 192, without exposing its construction. *)
Lemma special_interval_tree_limit_specification (R : realType) (H : nat -> {fset compact_real_intervals R}) :
  is_special_interval_tree_limit H (special_interval_tree_limit H).
Proof. exact: SpecialIntervalLimit.laws. Qed.

(** Source for [special_interval_tree_limit_compact]: supporting compactness
    of the selected limit A in 2.10.28(3), p. 192 This follows from the
    membership laws and finite compact levels, without a cost hypothesis. *)
Theorem special_interval_tree_limit_compact (R : realType) (H : nat -> {fset compact_real_intervals R}) :
  compact (special_interval_tree_limit H).
Proof. exact: (@interval_tree_limit_compact R H _ (@special_interval_tree_limit_specification R H)). Qed.
