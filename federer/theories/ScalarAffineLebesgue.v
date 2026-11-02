(** Supporting the integral-geometric cylinder assertion of Federer (1969),
    2.10.46, p. 204. Freilich (1950), Theorem 4.5, Part 3, pp. 244–245, uses
    scalar affine images of the one-dimensional factor. Their Lebesgue
    measures follow from Federer's 2.7.16(1), pp. 134–135, through the
    existing scalar/Euclidean identification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  EuclideanLebesgueDimensions EuclideanScalarLength LebesgueScalarMeasure
  EuclideanLebesgueTranslation ProjectedVolumeDilation AffineDilation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_lebesgue_embedding_volume]: supporting
    identification of the scalar and one-coordinate Lebesgue
    measures, 2.6.5, pp. 119–120, used in
    2.10.46, p. 204. Arbitrary sets are permitted. *)
Lemma scalar_lebesgue_embedding_volume (R : realType) (A : set R) :
  euclidean_lebesgue_measure 1 ((@euclidean_one_embed R) @` A)=lebesgue_scalar_measure A.
Proof.
rewrite euclidean_one_measure_scalar_image image_comp.
have he : (@euclidean_one_project R) \o (@euclidean_one_embed R)=id.
  by apply: funext=> x; rewrite /= euclidean_one_embedK.
by rewrite he image_id.
Qed.

(** Source for [scalar_affine_lebesgue_image]: supporting scalar
    affine image measure in 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 3,
    pp. 244–245. A nonzero slope gives the
    absolute-value factor on every set, including nonmeasurable
    sets and sets of infinite outer measure. *)
Theorem scalar_affine_lebesgue_image (R : realType) (a b : R) (T : set R) :
  a!=0%R -> lebesgue_scalar_measure ((fun t=>(a*t+b)%R) @` T)=
    `|a|%:E*lebesgue_scalar_measure T.
Proof.
move=> ha.
pose A := (@euclidean_one_embed R) @` T.
have hv := @euclidean_affine_dilation_volume R 1 A 0%R a.
have him : (@euclidean_one_project R) @`
    ((@affine_dilation R _ 0%R a) @` A)=(fun t=>(a*t)%R) @` T.
  apply/seteqP; split=> y.
  - move=> [z [x [t ht <-] <-] <-]; exists t=> //.
    by rewrite /euclidean_one_project /affine_dilation scaler0 add0r
      /euclidean_one_embed !ffunE.
  - move=> [t ht <-]; exists (affine_dilation 0%R a (euclidean_one_embed t)).
    + exists (euclidean_one_embed t); first by exists t.
      by [].
    + by rewrite /euclidean_one_project /affine_dilation scaler0 add0r
        /euclidean_one_embed !ffunE.
rewrite euclidean_one_measure_scalar_image him /A scalar_lebesgue_embedding_volume expr1 in hv.
have he : (fun t=>(a*t+b)%R) @` T=[set (b+t)%R | t in (fun t=>(a*t)%R) @` T].
  apply/seteqP; split=> y.
  - move=> [t ht <-]; exists (a*t)%R; first by exists t.
    by rewrite addrC.
  - move=> [z [t ht <-] <-]; exists t=> //; by rewrite addrC.
by rewrite he lebesgue_scalar_translation_set.
Qed.
