(** Public block extension supporting Federer (1969), 2.10.46, p. 204, and
    Freilich (1950), Theorem 4.5, Parts 6–7, pp. 247–250. All evaluation and
    orthogonality statements follow from the sealed block law. Source
    context and coordinate convention: EuclideanBlockExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  OrthogonalMaps EuclideanBlockExtensionUP EuclideanBlockExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_block_extension]: abstract transverse
    coordinate action for 2.10.46, p. 204;
    Freilich (1950), Part 6, pp. 247–249. *)
Definition euclidean_block_extension (R : realType) m n (h : {linear R_n R n -> R_n R n}) :=
  @EuclideanBlockExtension.value R m n h.

(** Source for [euclidean_block_extension_specification]: proved
    block law for 2.10.46, p. 204;
    Freilich (1950), Part 6, pp. 247–249. *)
Lemma euclidean_block_extension_specification (R : realType) m n (h : {linear R_n R n -> R_n R n}) :
  is_euclidean_block_extension h (@euclidean_block_extension R m n h).
Proof. exact: EuclideanBlockExtension.laws. Qed.

(** Source for [euclidean_block_extension_orthogonal]: supporting
    orthogonal transverse action in 2.10.46, p. 204;
    Freilich (1950), Part 6, pp. 247–249. *)
Lemma euclidean_block_extension_orthogonal (R : realType) m n (h : {linear R_n R n -> R_n R n}) :
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) h ->
  is_orthogonal_map (@euclidean_inner_product R (m+n)) (@euclidean_inner_product R (m+n))
    (@euclidean_block_extension R m n h).
Proof.
move=> hh; exact (@euclidean_block_extension_preserves_inner R m n h
  (@euclidean_block_extension R m n h) (@euclidean_block_extension_specification R m n h) hh).
Qed.
