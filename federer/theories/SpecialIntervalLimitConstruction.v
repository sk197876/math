(** Federer (1969), 2.10.28(3), p. 192: existence of a set satisfying the
    abstract intersection-of-level-unions laws. This elementary set
    comprehension is a witness, hidden behind opaque module ascription. The
    later mass proofs use only the membership specification. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [special_interval_tree_limit_exists]: direct
    existence witness for A in 2.10.28(3),
    p. 192. Every sequence of finite
    interval families has this set witness,
    independently of the subsequent measure hypotheses. *)
Lemma special_interval_tree_limit_exists (R : realType) (H : nat -> {fset compact_real_intervals R}) :
  exists A, is_special_interval_tree_limit H A.
Proof.
exists [set x : real_line_metric R | forall j, exists S, S \in H j /\ val S x].
by move=> x.
Qed.
