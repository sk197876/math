(** Federer (1969), 1.7.13, p. 37: the distance to a
    nonempty set, exposed solely through its infimum specification.
    The real-infimum existence witness remains private. Source
    editions and supporting reference: InnerSetDistanceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp.
From Federer Require Import InnerProductUP InnerSetDistanceUP InnerSetDistanceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type InnerSetDistanceSig.
(** Source for [distance]: Federer 1.7.13, p. 37,
    the specified distance from a point to a nonempty set. *)
Parameter distance : forall (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V) (C : set V),
    C !=set0 -> R.
(** Source for [laws]: Federer 1.7.13, p. 37,
    the exported distance satisfies the defining infimum laws. *)
Parameter laws : forall (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V) (C : set V)
    (hne : C !=set0),
    is_inner_set_distance hB a C (@distance R V B hB a C hne).
End InnerSetDistanceSig.
Module InnerSetDistance : InnerSetDistanceSig.
(** Source for [distance]: Federer 1.7.13, p. 37,
    select the proved distance witness within the opaque module. *)
Definition distance (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V) (C : set V)
    (hne : C !=set0) : R :=
  sval (constructive_indefinite_description (inner_set_distance_exists hB a hne)).
(** Source for [laws]: Federer 1.7.13, p. 37,
    the selected witness obeys the exported infimum specification. *)
Lemma laws (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V) (C : set V)
    (hne : C !=set0) :
  is_inner_set_distance hB a C (@distance R V B hB a C hne).
Proof. exact: (svalP (constructive_indefinite_description (inner_set_distance_exists hB a hne))). Qed.
End InnerSetDistance.
