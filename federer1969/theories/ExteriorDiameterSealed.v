(** Opaque exterior-diameter interface for Federer (1969), 2.10.3, p. 171.
    Only the least-upper-bound specification is exposed. Source context and
    auxiliary empty-set convention: ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations ExteriorDiameterUP ExteriorDiameterConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ExteriorDiameterSignature.
(** Source for [value]: abstract exterior-product supremum
    used in Federer 2.10.3, p. 171. *)
Parameter value : forall (R : realType) (n m : nat), set (R_n R n) -> \bar R.
(** Source for [laws]: least-upper-bound laws for the
    exterior-product supremum of Federer 2.10.3, p. 171. *)
Parameter laws : forall (R : realType) (n m : nat) (A : set (R_n R n)),
  is_exterior_diameter m A (@value R n m A).
End ExteriorDiameterSignature.
Module ExteriorDiameter : ExteriorDiameterSignature.
(** Source for [value]: private choice from the proved
    existence result for Federer 2.10.3, p. 171. *)
Definition value (R : realType) (n m : nat) (A : set (R_n R n)) :=
  projT1 (cid (@exterior_diameter_exists R n m A)).
(** Source for [laws]: proved supremum laws for the
    selected witness of Federer 2.10.3, p. 171. *)
Lemma laws (R : realType) (n m : nat) (A : set (R_n R n)) :
  is_exterior_diameter m A (@value R n m A).
Proof. exact: projT2 (cid (@exterior_diameter_exists R n m A)). Qed.
End ExteriorDiameter.
