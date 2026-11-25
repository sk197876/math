(** Opaque limit-set witness for Federer (1969), 2.10.28(3), p. 192. Only
    this sealing module imports the set comprehension witness. Public proofs
    use the abstract membership laws. Source context:
    SpecialIntervalFamilyUP.v. *)
(** Federer 2.10.28, pp. 192–193: source context and the abstract laws are
    recorded in the corresponding specification module. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP SpecialIntervalLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type SPECIAL_INTERVAL_LIMIT.
(** Source for [value]: limit A in 2.10.28(3),
    p. 192, exposed as an abstract set. *)
Parameter value : forall (R : realType), (nat -> {fset compact_real_intervals R}) -> set (real_line_metric R).
(** Source for [laws]: defining intersection-of-unions
    membership in 2.10.28(3), p. 192. *)
Parameter laws : forall (R : realType) (H : nat -> {fset compact_real_intervals R}),
  is_special_interval_tree_limit H (@value R H).
End SPECIAL_INTERVAL_LIMIT.

Module SpecialIntervalLimit : SPECIAL_INTERVAL_LIMIT.
(** Source for [value]: proved witness of the
    limit set in 2.10.28(3), p. 192,
    hidden by opaque module ascription. *)
Definition value (R : realType) (H : nat -> {fset compact_real_intervals R}) :=
  projT1 (cid (@special_interval_tree_limit_exists R H)).
(** Source for [laws]: limit membership laws in
    2.10.28(3), p. 192, from the
    proved set-theoretic existence witness. *)
Lemma laws (R : realType) (H : nat -> {fset compact_real_intervals R}) :
  is_special_interval_tree_limit H (@value R H).
Proof. exact: (projT2 (cid (@special_interval_tree_limit_exists R H))). Qed.
End SpecialIntervalLimit.
