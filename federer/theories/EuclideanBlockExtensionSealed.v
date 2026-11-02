(** Opaque block extension supporting Federer (1969), 2.10.46,
    p. 204. Only the linear map and its block specification
    are exposed. Source details: EuclideanBlockExtensionUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanBlockExtensionUP EuclideanBlockExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type EUCLIDEAN_BLOCK_EXTENSION.
(** Source for [value]: abstract transverse block action for
    2.10.46, p. 204; Freilich (1950), Part 6, pp. 247–249. *)
Parameter value : forall (R : realType) m n (h : {linear R_n R n -> R_n R n}),
  {linear R_n R (m+n) -> R_n R (m+n)}.
(** Source for [laws]: defining block law supporting 2.10.46,
    p. 204; Freilich (1950), Part 6, pp. 247–249. *)
Parameter laws : forall (R : realType) m n h, is_euclidean_block_extension h (@value R m n h).
End EUCLIDEAN_BLOCK_EXTENSION.
Module EuclideanBlockExtension : EUCLIDEAN_BLOCK_EXTENSION.
(** Source for [value]: selected proved witness for 2.10.46,
    p. 204, hidden by opaque ascription. *)
Definition value (R : realType) m n h := projT1 (cid (@euclidean_block_extension_exists R m n h)).
(** Source for [laws]: proof of the exposed law supporting
    2.10.46, p. 204; no project axiom is introduced. *)
Lemma laws (R : realType) m n h : is_euclidean_block_extension h (@value R m n h).
Proof. exact: projT2 (cid (@euclidean_block_extension_exists R m n h)). Qed.
End EuclideanBlockExtension.
