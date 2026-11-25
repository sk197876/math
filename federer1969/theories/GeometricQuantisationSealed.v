(** Opaque geometric approximant for Federer (1969), 2.4.4(2), proof p. 83.
    Source context: GeometricQuantisationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GeometricQuantisationUP GeometricQuantisationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type GeometricQuantisationSignature.
(** Source for [value]: abstract geometric approximant in
    Federer 2.4.4(2), p. 83, for a base greater than one. *)
Parameter value : forall (R : realType) (t : R), 1 < t -> R -> R.
(** Source for [laws]: geometric cell and zero-value laws
    of Federer 2.4.4(2), p. 83. *)
Parameter laws : forall (R : realType) (t : R) (ht : 1 < t),
  is_geometric_quantisation t (@value R t ht).
End GeometricQuantisationSignature.
Module GeometricQuantisation : GeometricQuantisationSignature.
(** Source for [value]: private witness selection for the
    geometric approximant in Federer 2.4.4(2), p. 83. *)
Definition value (R : realType) (t : R) (ht : 1 < t) :=
  projT1 (cid (@geometric_quantisation_exists R t ht)).
(** Source for [laws]: the selected witness satisfies the
    geometric laws in Federer 2.4.4(2), p. 83. *)
Lemma laws (R : realType) (t : R) (ht : 1 < t) :
  is_geometric_quantisation t (@value R t ht).
Proof. exact: projT2 (cid (@geometric_quantisation_exists R t ht)). Qed.
End GeometricQuantisation.
