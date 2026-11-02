(** Opaque selected parameter family for Federer (1969), 2.8.10, p. 147. The
    maximal-family witness is hidden; subsequent proofs use only the two
    stated selection laws. Source context: RadiusCoverSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP RadiusCoverSelectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type RadiusCoverSelectionSignature.
(** Source for [value]: the subset R chosen in Federer
    2.8.10, p. 147, exposed only through its laws. *)
Parameter value : forall (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R)),
  1 < tau -> 0 < mu -> is_bounded_positive_radius_family mu Q -> set (X * R).
(** Source for [laws]: conditions (1) and (2) in Federer
    2.8.10, p. 147, together with R subset Q. *)
Parameter laws : forall (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q),
  is_radius_cover_selection tau Q (@value R X tau mu Q ht hm hQ).
End RadiusCoverSelectionSignature.

Module RadiusCoverSelection : RadiusCoverSelectionSignature.
(** Source for [value]: private choice of the proved
    witness for Federer 2.8.10, p. 147. *)
Definition value (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q) :=
  projT1 (cid (@radius_cover_selection_exists R X tau mu Q ht hm hQ)).
(** Source for [laws]: the selected witness satisfies the
    specification of Federer 2.8.10, p. 147. *)
Lemma laws (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q) :
  is_radius_cover_selection tau Q (@value R X tau mu Q ht hm hQ).
Proof. exact: projT2 (cid (@radius_cover_selection_exists R X tau mu Q ht hm hQ)). Qed.
End RadiusCoverSelection.
