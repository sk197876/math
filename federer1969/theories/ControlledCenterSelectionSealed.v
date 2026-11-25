(** Opaque controlled center-covering selection for Federer (1969), 2.8.13,
    pp. 149–150. The maximal-family proof is hidden, exposing only
    membership, controlledness and center coverage. Source context:
    ControlledCenterSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP ControlledCenterSelectionUP ControlledCenterSelectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type ControlledCenterSelectionSignature.
(** Source for [value]: the controlled subset chosen in Federer
    2.8.13, pp. 149–150, exposed only through its laws. *)
Parameter value : forall (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R)),
  1 < tau -> 0 < mu -> is_bounded_positive_radius_family mu Q -> set (X * R).
(** Source for [laws]: membership in the eligible family,
    controlledness and center coverage in Federer 2.8.13,
    pp. 149–150. *)
Parameter laws : forall (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q),
  is_controlled_center_selection tau Q (@value R X tau mu Q ht hm hQ).
End ControlledCenterSelectionSignature.

Module ControlledCenterSelection : ControlledCenterSelectionSignature.
(** Source for [value]: private choice of the proved
    witness for Federer 2.8.13, pp. 149–150. *)
Definition value (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q) :=
  projT1 (cid (@controlled_center_selection_exists R X tau mu Q ht hm hQ)).
(** Source for [laws]: the selected witness satisfies the
    specification of Federer 2.8.13, pp. 149–150. *)
Lemma laws (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R))
    (ht : 1 < tau) (hm : 0 < mu) (hQ : is_bounded_positive_radius_family mu Q) :
  is_controlled_center_selection tau Q (@value R X tau mu Q ht hm hQ).
Proof. exact: projT2 (cid (@controlled_center_selection_exists R X tau mu Q ht hm hQ)). Qed.
End ControlledCenterSelection.
