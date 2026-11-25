(** Federer (1969), 2.6.5, p. 120:
    the existing finite Cartesian block identification,
    specialised to R^3=R^2 times R.
    These exact coordinate connections support the
    implicit graph in 3.4.10, p. 338. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_three_prefix_first]: the
    first coordinate is retained by the original
    Cartesian projection, 2.6.5, p. 120,
    supporting 3.4.10, p. 338. *)
Lemma euclidean_three_prefix_first (R:realType) (v:R_n R 3):
  @euclidean_first_block_map R 2 1 v ord0=v ord0.
Proof.
rewrite /euclidean_first_block_map /euclidean_first_block ffunE.
congr (v _);exact:val_inj.
Qed.

(** Source for [euclidean_three_prefix_second]: the
    second original coordinate is the last
    prefix coordinate, 2.6.5, p. 120,
    supporting the (x,z) auxiliary prefix in
    3.4.10, p. 338. *)
Lemma euclidean_three_prefix_second (R:realType) (v:R_n R 3):
  @euclidean_first_block_map R 2 1 v ord_max=v (Ordinal (isT:(1<3)%N)).
Proof.
rewrite /euclidean_first_block_map /euclidean_first_block ffunE.
congr (v _);exact:val_inj.
Qed.

(** Source for [euclidean_three_suffix]: the last
    original coordinate is the unique suffix
    coordinate, 2.6.5, p. 120, supporting
    the implicit t coordinate in 3.4.10, p. 338. *)
Lemma euclidean_three_suffix (R:realType) (v:R_n R 3):
  @euclidean_last_block_map R 2 1 v ord0=v ord_max.
Proof.
rewrite /euclidean_last_block_map /euclidean_last_block ffunE.
congr (v _);exact:val_inj.
Qed.
