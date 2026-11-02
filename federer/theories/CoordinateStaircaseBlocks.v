(** Federer (1969), 3.1.4, p. 215: the earlier-coordinate
    increments in the stair path are the first block in the Fubini
    decomposition. These identities include empty coordinate blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinear ConcatenatedFamilies EuclideanSliceTranslation EuclideanCoordinateStaircase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_prefix_block_join]: the prefix
    (v_1,...,v_k,0,...,0) used to define S_i in Federer
    3.1.4, p. 215, is the first block embedded with zero second block. *)
Lemma coordinate_prefix_block_join (R : realType) k l
    (u : R_n R k) (v : R_n R l) :
  coordinate_prefix (@euclidean_block_join R k l (u,v)) k=
    @euclidean_block_join R k l (u,0).
Proof.
apply: euclidean_block_vectors_ext.
- move=> j; by rewrite /coordinate_prefix ffunE /= ltn_ord !euclidean_block_join_left.
- move=> j; rewrite /coordinate_prefix ffunE /= ltnNge leq_addr /= euclidean_block_join_right.
  by rewrite ffunE.
Qed.

(** Source for [euclidean_slice_translation_prefix]: the point
    a+(v_1,...,v_k,0,...,0) in Federer 3.1.4, p. 215,
    equals the translated first-block slice from 3.1.3(4). *)
Lemma euclidean_slice_translation_prefix (R : realType) k l
    (a h : R_n R (k+l)) :
  @euclidean_slice_translation R k l a (@euclidean_block_split R k l h).1=
    a+coordinate_prefix h k.
Proof.
have hp := coordinate_prefix_block_join (@euclidean_block_split R k l h).1
  (@euclidean_block_split R k l h).2.
rewrite -surjective_pairing euclidean_block_splitK in hp.
rewrite hp /euclidean_slice_translation; apply: euclidean_block_vectors_ext.
- move=> j; by rewrite euclidean_block_join_left !ffunE !concatenate_family_l
    /euclidean_block_split /= !ffunE.
- move=> j; by rewrite euclidean_block_join_right !ffunE !concatenate_family_r
    /euclidean_block_split /= !ffunE addr0.
Qed.
