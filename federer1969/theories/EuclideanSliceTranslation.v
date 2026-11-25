(** Federer (1969), 3.1.3(4), p. 213: the linear epimorphism
    alpha(u,v,z)=(u+z,v), with u,z in R^k and v in R^l.
    The formulas are the printed coordinate map, including empty blocks. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinear ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SliceTranslation.
Variable R : realType.
Variables k l : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [euclidean_slice_translation]: the map (u,v,z) to
    (u+z,v) in Federer 3.1.3(4), p. 213, written with the first two
    coordinate blocks joined into a single parameter x. *)
Definition euclidean_slice_translation (x : E (k+l)) (z : E k) : E (k+l) :=
  euclidean_block_join ((euclidean_block_split x).1+z,(euclidean_block_split x).2).

(** Source for [euclidean_slice_translation_zero]: the translated
    function has the original value at z=0, Federer 3.1.3(4), p. 213. *)
Lemma euclidean_slice_translation_zero x : euclidean_slice_translation x 0=x.
Proof. by rewrite /euclidean_slice_translation addr0 -surjective_pairing euclidean_block_splitK. Qed.

(** Source for [euclidean_slice_translation_blocks]: the literal
    (u+z,v) evaluation of alpha in Federer 3.1.3(4), p. 213. *)
Lemma euclidean_slice_translation_blocks u v z :
  euclidean_slice_translation (euclidean_block_join (u,v)) z=euclidean_block_join (u+z,v).
Proof. by rewrite /euclidean_slice_translation euclidean_block_joinK. Qed.

(** Source for [euclidean_slice_sum]: alpha in Federer 3.1.3(4),
    p. 213, viewed as a map between Euclidean coordinate spaces. *)
Definition euclidean_slice_sum (w : R_n R ((k+l)+k)) : R_n R (k+l) :=
  euclidean_slice_translation (euclidean_block_split w).1 (euclidean_block_split w).2.

(** Source for [euclidean_slice_sum_linear]: supporting linearity
    of alpha, as required for applying (3) in Federer 3.1.3(4), p. 213. *)
Lemma euclidean_slice_sum_linear : linear euclidean_slice_sum.
Proof.
move=> t x y; apply: euclidean_block_vectors_ext.
- move=> i; rewrite /euclidean_slice_sum /euclidean_slice_translation
    euclidean_block_join_left !ffunE !concatenate_family_l
    /euclidean_block_split /= !ffunE.
  by rewrite scalerDr addrACA.
- move=> i; by rewrite /euclidean_slice_sum /euclidean_slice_translation
    euclidean_block_join_right !ffunE !concatenate_family_r
    /euclidean_block_split /= !ffunE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (R_n R ((k+l)+k)) (R_n R (k+l)) *:%R
  euclidean_slice_sum euclidean_slice_sum_linear.

(** Source for [euclidean_slice_sum_surjective]: alpha is an
    epimorphism, Federer 3.1.3(4), p. 213. A preimage of x is (x,0). *)
Lemma euclidean_slice_sum_surjective y : exists x, euclidean_slice_sum x=y.
Proof.
exists (@euclidean_block_join R (k+l) k (y,0)).
by rewrite /euclidean_slice_sum euclidean_block_joinK euclidean_slice_translation_zero.
Qed.
End SliceTranslation.
