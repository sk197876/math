(** Federer (1969), 2.4.12, p. 87: sealed dense candidate sequences
    supporting finite-image approximation. Source context and mathematical
    role: SeparablePointSequenceUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import SeparablePointSequenceUP SeparablePointSequenceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SeparablePointSequenceSignature.
(** Source for [value]: abstract supporting dense sequence for
    Federer 2.4.12, p. 87, with a prescribed first point. *)
Parameter value : forall (R : realType) (Y : metricType R) (y0 : Y) (D : set Y),
  countable D -> dense D -> nat -> Y.
(** Source for [laws]: first-value and density laws supporting
    finite-image approximation in Federer 2.4.12, p. 87. *)
Parameter laws : forall (R : realType) (Y : metricType R) (y0 : Y) (D : set Y)
  (hc : countable D) (hd : dense D), is_based_dense_sequence y0 (@value R Y y0 D hc hd).
End SeparablePointSequenceSignature.
Module SeparablePointSequence : SeparablePointSequenceSignature.
(** Source for [value]: private selection of a proved dense
    sequence witness supporting Federer 2.4.12, p. 87. *)
Definition value (R : realType) (Y : metricType R) (y0 : Y) (D : set Y)
    (hc : countable D) (hd : dense D) :=
  projT1 (cid (@based_dense_sequence_exists R Y y0 D hc hd)).
(** Source for [laws]: the selected sequence satisfies the exposed
    laws supporting Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (Y : metricType R) (y0 : Y) (D : set Y)
    (hc : countable D) (hd : dense D) : is_based_dense_sequence y0 (@value R Y y0 D hc hd).
Proof. exact: projT2 (cid (@based_dense_sequence_exists R Y y0 D hc hd)). Qed.
End SeparablePointSequence.
