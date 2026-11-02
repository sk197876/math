(** Federer (1969), 2.2.16, p. 71: opaque maximal separated subsets. The
    Zorn witness stays private; subsequent proofs use inclusion, separation
    and maximality. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SeparatedMetricSetUP MaximalSeparatedConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MaximalSeparatedSignature.
(** Source for [value]: abstract maximal separated set
    chosen in Federer 2.2.16, p. 71. *)
Parameter value : forall (R : realType) (X : metricType R), set X -> R -> set X.
(** Source for [laws]: inclusion, strict separation and
    maximality in Federer 2.2.16, p. 71. *)
Parameter laws : forall (R : realType) (X : metricType R) (A : set X) r,
  is_maximal_separated_subset A r (@value R X A r).
End MaximalSeparatedSignature.
Module MaximalSeparated : MaximalSeparatedSignature.
(** Source for [value]: private selection of the proved
    maximal-set witness for Federer 2.2.16, p. 71. *)
Definition value (R : realType) (X : metricType R) (A : set X) r :=
  projT1 (cid (@maximal_separated_subset_exists R X A r)).
(** Source for [laws]: the selected set satisfies the
    maximality specification of Federer 2.2.16, p. 71. *)
Lemma laws (R : realType) (X : metricType R) (A : set X) r :
  is_maximal_separated_subset A r (@value R X A r).
Proof. exact: projT2 (cid (@maximal_separated_subset_exists R X A r)). Qed.
End MaximalSeparated.
