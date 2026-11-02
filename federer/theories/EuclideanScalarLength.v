(** Supporting scalar identification for the degree-one observation in
    Federer (1969), 2.10.4, p. 172. The Euclidean measure L^1 from 2.6.5,
    pp. 119–120, is the image of scalar Lebesgue measure under the
    one-coordinate isometry. Expose its all-set identity and the contraction
    of scalar orthogonal projections. Source context for the product
    identification: EuclideanOneCoordinate.v; for projections:
    ProjectedVolumeGaugeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric InnerNormedTopology EuclideanOneCoordinate EuclideanLebesgue
  EuclideanLebesgueDimensions EuclideanBallVolume LebesgueScalarMeasure MeasurePushforward CoordinateProjection
  ProjectionNorm RealMetricBackground TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scalar_projection]: supporting
    scalar form of a one-dimensional projection in
    Federer 2.10.4, p. 172. Use the already
    linear coordinate-head map and linear composition. *)
Definition euclidean_scalar_projection (R : realType) (n : nat)
    (p : {linear R_n R n -> R_n R 1}) : {linear R_n R n -> R^o} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (@coordinate_head R 0) _) p.

(** Source for [euclidean_scalar_projectionE]: supporting
    evaluation of the scalar projection for the degree-
    one formula in Federer 2.10.4, p. 172. *)
Lemma euclidean_scalar_projectionE (R : realType) (n : nat)
    (p : {linear R_n R n -> R_n R 1}) (x : R_n R n) :
  euclidean_scalar_projection p x=euclidean_one_project (p x).
Proof. by []. Qed.

(** Source for [euclidean_one_measure_scalar_image]: supporting
    actual L^1 identification in Federer 2.10.4,
    p. 172, from the first-factor law of 2.6.5,
    pp. 119–120. Arbitrary, possibly nonmeasurable,
    sets are included by the inverse identities. *)
Lemma euclidean_one_measure_scalar_image (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 1))) :
  euclidean_lebesgue_measure 1 A=
    LebesgueScalarMeasure.lebesgue_scalar_measure ((@euclidean_one_project R) @` A).
Proof.
change (@positive_euclidean_lebesgue_measure R 0 A=
  lebesgue_scalar_measure ((@euclidean_one_project R) @` A)).
rewrite positive_euclidean_lebesgue_first /measure_pushforward.
congr (LebesgueScalarMeasure.lebesgue_scalar_measure _).
apply/seteqP; split=> t /=.
- move=> ht; exists (euclidean_one_embed t)=> //; by rewrite euclidean_one_embedK.
- move=> [x hx <-]; by rewrite euclidean_one_projectK.
Qed.

(** Source for [euclidean_scalar_orthogonal_projection_nonexpanding]:
    supporting scalar contraction for the degree-one
    projection formula in Federer 2.10.4, p. 172,
    from 1.7.7, p. 34, and the actual norm
    on the one-dimensional Euclidean target. *)
Lemma euclidean_scalar_orthogonal_projection_nonexpanding (R : realType) (n : nat)
    (p : {linear R_n R n -> R_n R 1}) : O_star p ->
  forall x y : inner_metric_space (@euclidean_inner_productP R n),
    mdist (euclidean_one_project (p x) : real_line_metric R) (euclidean_one_project (p y))<=mdist x y.
Proof.
move=> hp x y.
rewrite real_line_metric_distanceE /euclidean_one_project !inner_metric_distanceE.
have hh := @orthogonal_projection_norm_bound R (R_n R n) (R_n R 1)
  (@euclidean_inner_product R n) (@euclidean_inner_product R 1)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R 1) p ((O_star_projection p).1 hp) (x-y).
rewrite -(@inner_norm_topologyE R (R_n R 1) (@euclidean_inner_product R 1)
  (@euclidean_inner_productP R 1)) euclidean_norm_one linearB !ffunE in hh.
exact hh.
Qed.
