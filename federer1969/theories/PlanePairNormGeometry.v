(** Federer (1969), 2.10.44, printed p. 202: compare the coordinate supremum
    norm mu and Euclidean norm nu on the displayed coordinate pairs. Use the
    existing public Cartesian pairing, the opaque supremum norm laws and the
    existing Euclidean squared-distance identity. These are coordinate
    adapters for the printed counterexample, not new claims of Federer. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanRealPlane EuclideanBlockCoordinates EuclideanOneCoordinate RealMetricBackground
  NormMetric PlaneSupremumNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_plane_first_coordinateE]: supporting
    first-coordinate adapter for the Euclidean
    distances in 2.10.44, p. 202. *)
Lemma real_plane_first_coordinateE (R : realType)
    (p : inner_metric_space (@euclidean_inner_productP R 2)) :
  euclidean_real_plane_first p=p ord0.
Proof.
rewrite /euclidean_real_plane_first /euclidean_one_project /euclidean_block_split ffunE.
congr (p _); exact: val_inj.
Qed.

(** Source for [real_plane_second_coordinateE]: supporting
    second-coordinate adapter for the Euclidean
    distances in 2.10.44, p. 202. *)
Lemma real_plane_second_coordinateE (R : realType)
    (p : inner_metric_space (@euclidean_inner_productP R 2)) :
  euclidean_real_plane_second p=p ord_max.
Proof.
rewrite /euclidean_real_plane_second /euclidean_one_project /euclidean_block_split ffunE.
congr (p _); exact: val_inj.
Qed.

(** Source for [real_plane_pair_first_coordinate]: supporting
    first coordinate of the displayed points in
    2.10.44, p. 202, using the existing Cartesian pairing. *)
Lemma real_plane_pair_first_coordinate (R : realType) (x y : R) :
  (@euclidean_real_plane_pair R x y) ord0=x.
Proof.
by rewrite -real_plane_first_coordinateE /euclidean_real_plane_first /euclidean_real_plane_pair
  euclidean_block_joinK euclidean_one_embedK.
Qed.

(** Source for [real_plane_pair_second_coordinate]: supporting
    second coordinate of the displayed points in
    2.10.44, p. 202, using the existing Cartesian pairing. *)
Lemma real_plane_pair_second_coordinate (R : realType) (x y : R) :
  (@euclidean_real_plane_pair R x y) ord_max=y.
Proof.
by rewrite -real_plane_second_coordinateE /euclidean_real_plane_second /euclidean_real_plane_pair
  euclidean_block_joinK euclidean_one_embedK.
Qed.

(** Source for [euclidean_plane_squared_distance_coordinates]: direct
    coordinate formula for nu-distance in 2.10.44,
    p. 202, derived from the previously proved
    actual Euclidean Cartesian squared-distance law. *)
Lemma euclidean_plane_squared_distance_coordinates (R : realType)
    (p q : inner_metric_space (@euclidean_inner_productP R 2)) :
  mdist p q^+2=(p ord0-q ord0)^+2+(p ord_max-q ord_max)^+2.
Proof.
by rewrite euclidean_real_plane_squared_distance !real_plane_first_coordinateE !real_plane_second_coordinateE
  -!normrX !ger0_norm ?sqr_ge0.
Qed.

(** Source for [supremum_plane_pair_distance]: direct
    mu-distance formula for the coordinate pairs
    in 2.10.44, p. 202. The supremum norm
    is used only through its derived evaluation law. *)
Lemma supremum_plane_pair_distance (R : realType) (a b c d : R) :
  @mdist R [the metricType R of plane_supremum_metric R]
    (euclidean_real_plane_pair a b) (euclidean_real_plane_pair c d)=
    Num.max `|a-c| `|b-d|.
Proof.
rewrite real_norm_metric_distanceE plane_supremum_normE.
rewrite [((euclidean_real_plane_pair a b-euclidean_real_plane_pair c d) ord0)]ffunE
  [((euclidean_real_plane_pair a b-euclidean_real_plane_pair c d) ord_max)]ffunE.
rewrite [((-euclidean_real_plane_pair c d) ord0)]ffunE
  [((-euclidean_real_plane_pair c d) ord_max)]ffunE.
by rewrite !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate.
Qed.
