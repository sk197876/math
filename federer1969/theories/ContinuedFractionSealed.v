(** Federer (1969), 2.2.9, p. 65, opaque interface for the classical
    continued-fraction map. It exposes the ordinary-truncation limit law and
    the proved homeomorphism property. The four-digit tree, regrouping and
    choice witness remain implementation details. Source context and
    supporting references: ContinuedFractionBranches.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace RealMetricBackground RationalRealUP
  HomeomorphismOnto ContinuedFractionLimitUP ContinuedFractionEmbeddingConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ContinuedFractionSignature.
(** Source for [value]: the classical limit map mentioned in
    Federer 2.2.9, p. 65, with ordinary positive digits. *)
Parameter value : forall R : realType, positive_sequence_space R -> real_line_metric R.
(** Source for [laws]: the literal continued-fraction limit
    specification in Federer 2.2.9, p. 65. *)
Parameter laws : forall R, is_continued_fraction_map (@value R).
(** Source for [homeomorphism]: the homeomorphism onto ordinary
    irrational points of (0,1) in Federer 2.2.9, p. 65. *)
Parameter homeomorphism : forall R,
  is_homeomorphism_onto (@irrational_unit_interval R : set (real_line_metric R)) (@value R).
End ContinuedFractionSignature.
Module ContinuedFraction : ContinuedFractionSignature.
(** Source for [value]: hidden choice from the fully proved
    existence theorem for Federer 2.2.9, p. 65. *)
Definition value (R : realType) :=
  projT1 (cid (continued_fraction_homeomorphism_exists R)).
(** Source for [laws]: ordinary-truncation convergence from the
    proved existence witness for Federer 2.2.9, p. 65. *)
Lemma laws (R : realType) : is_continued_fraction_map (@value R).
Proof. exact: (projT2 (cid (continued_fraction_homeomorphism_exists R))).1. Qed.
(** Source for [homeomorphism]: homeomorphism property from the
    same proved witness for Federer 2.2.9, p. 65. *)
Lemma homeomorphism (R : realType) :
  is_homeomorphism_onto (@irrational_unit_interval R : set (real_line_metric R)) (@value R).
Proof. exact: (projT2 (cid (continued_fraction_homeomorphism_exists R))).2. Qed.
End ContinuedFraction.
