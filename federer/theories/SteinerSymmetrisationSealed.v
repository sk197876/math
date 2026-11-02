(** Opaque existence witness for Steiner symmetrisation in Federer (1969),
    2.10.30, p. 195. Expose only the unit-normal and line-section laws.
    Source context: SteinerSymmetrisationUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric CoveringFamilyUP
  SteinerSymmetrisationUP SteinerSymmetrisationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type STEINER_SYMMETRISATION.
(** Source for [value]: abstract bounded-set operation
    of 2.10.30, p. 195, for an arbitrary
    unit normal in an inner-product space. *)
Parameter value : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (u : V), B u u= 1 -> forall S : set (inner_metric_space hB),
  metric_set_bounded S -> set V.
(** Source for [laws]: direct line-section characterisation
    in 2.10.30, p. 195. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB))
  (hb : metric_set_bounded S),
  is_steiner_symmetrisation hB u S (@value R V B hB u hu S hb).
End STEINER_SYMMETRISATION.

Module SteinerSymmetrisation : STEINER_SYMMETRISATION.
(** Source for [value]: proved section-gluing witness
    for 2.10.30, p. 195, hidden by opaque
    module ascription. *)
Definition value (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB))
    (hb : metric_set_bounded S) :=
  projT1 (cid (@steiner_symmetrisation_exists R V B hB u hu S hb)).
(** Source for [laws]: proved abstract section laws
    for 2.10.30, p. 195. *)
Lemma laws (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB))
    (hb : metric_set_bounded S) :
  is_steiner_symmetrisation hB u S (@value R V B hB u hu S hb).
Proof. exact: (projT2 (cid (@steiner_symmetrisation_exists R V B hB u hu S hb))). Qed.
End SteinerSymmetrisation.
