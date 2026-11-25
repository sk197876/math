(** Public weak enlargement interface for the Hausdorff application in
    Federer (1969), 2.10.24, p. 188. Source context and precise
    interpretation: ClosedHausdorffEnlargementUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffDiameterCost CaratheodoryWeakEnlargementUP ClosedHausdorffEnlargementUP
  ClosedHausdorffEnlargementSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_hausdorff_enlargement]: public sealed
    containing enlargement for closed Hausdorff generators,
    supporting 2.10.24, p. 188. *)
Definition closed_hausdorff_enlargement (R : realType) (X : metricType R) (m : nat) :=
  @ClosedHausdorffEnlargement.value R X m.

(** Source for [closed_hausdorff_enlargement_specification]:
    public nonnegative cost, containment, diameter and
    cost bounds for the Hausdorff application of
    2.10.24, p. 188. Zero costs and unbounded
    closed generators retain their original conventions. *)
Lemma closed_hausdorff_enlargement_specification (R : realType) (X : metricType R) (m : nat) :
  is_weak_caratheodory_enlargement [set S : set X | closed S /\ S!=set0]
    (@hausdorff_diameter_cost R X m) (@closed_hausdorff_enlargement R X m)
    (closed_hausdorff_enlargement_control R m).
Proof. exact: ClosedHausdorffEnlargement.laws. Qed.
