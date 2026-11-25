(** Opaque enlargement witness for the Hausdorff application in Federer
    (1969), 2.10.24, p. 188. Source context and the weak-zero-cost
    interpretation: ClosedHausdorffEnlargementUP.v. The implementation is
    exposed only through its proved containing, diameter and cost laws. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffDiameterCost CaratheodoryWeakEnlargementUP ClosedHausdorffEnlargementUP
  ClosedHausdorffEnlargementConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type ClosedHausdorffEnlargementSignature.
(** Source for [value]: abstract containing enlargement
    supporting Federer 2.10.24, p. 188. *)
Parameter value : forall (R : realType) (X : metricType R), nat -> set X -> set X.
(** Source for [laws]: proved weak enlargement laws for
    the Hausdorff application of 2.10.24, p. 188. *)
Parameter laws : forall (R : realType) (X : metricType R) (m : nat),
  is_weak_caratheodory_enlargement [set S : set X | closed S /\ S!=set0]
    (@hausdorff_diameter_cost R X m) (@value R X m) (closed_hausdorff_enlargement_control R m).
End ClosedHausdorffEnlargementSignature.
Module ClosedHausdorffEnlargement : ClosedHausdorffEnlargementSignature.
(** Source for [value]: private selection of the proved
    enlargement witness for Federer 2.10.24, p. 188. *)
Definition value (R : realType) (X : metricType R) (m : nat) :=
  projT1 (cid (@closed_hausdorff_enlargement_exists R X m)).
(** Source for [laws]: the selected witness satisfies
    the weak enlargement laws for 2.10.24, p. 188. *)
Lemma laws (R : realType) (X : metricType R) (m : nat) :
  is_weak_caratheodory_enlargement [set S : set X | closed S /\ S!=set0]
    (@hausdorff_diameter_cost R X m) (@value R X m) (closed_hausdorff_enlargement_control R m).
Proof. exact: projT2 (cid (@closed_hausdorff_enlargement_exists R X m)). Qed.
End ClosedHausdorffEnlargement.
