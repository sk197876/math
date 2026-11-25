(** Opaque coordinate-supremum norm for Federer (1969), 2.10.44, printed p.
    202. Expose the norm function with its proved least-coordinate-bound
    laws. Source context: PlaneSupremumNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations PlaneSupremumNormUP PlaneSupremumNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type PLANE_SUPREMUM_NORM.
(** Source for [value]: abstract norm mu in
    2.10.44, p. 202, with implementation hidden. *)
Parameter value : forall R : realType, R_n R 2 -> R.
(** Source for [laws]: abstract supremum laws
    for mu in 2.10.44, p. 202. *)
Parameter laws : forall R : realType, is_plane_supremum_norm (@value R).
End PLANE_SUPREMUM_NORM.
Module PlaneSupremumNorm : PLANE_SUPREMUM_NORM.
(** Source for [value]: privately proved coordinate-
    supremum witness for 2.10.44, p. 202,
    hidden by opaque module ascription. *)
Definition value (R : realType) := projT1 (cid (@plane_supremum_norm_exists R)).
(** Source for [laws]: proved supremum specification
    of the opaque norm in 2.10.44, p. 202. *)
Lemma laws (R : realType) : is_plane_supremum_norm (@value R).
Proof. exact: (projT2 (cid (@plane_supremum_norm_exists R))). Qed.
End PlaneSupremumNorm.
