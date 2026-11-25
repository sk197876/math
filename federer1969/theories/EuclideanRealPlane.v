(** Federer (1969), 2.10.29, pp. 193–194: realise the two scalar factors in
    the actual Euclidean plane, rather than a replacement product metric.
    The usual block identification of 2.6.5, p. 120, and the one-dimensional
    Euclidean isometry provide the pairing, projections and squared-distance
    law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanMetricProduct
  EuclideanBallVolume RealMetricBackground MetricCartesianProductUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Plane.
Variable R : realType.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [euclidean_one_project_distance]: supporting
    one-dimensional isometry in 2.10.29, p. 194,
    from 1.7.1, p. 28, for the existing
    Euclidean norm and scalar absolute value. *)
Lemma euclidean_one_project_distance (x y : E 1) :
  mdist x y=mdist (euclidean_one_project x : real_line_metric R) (euclidean_one_project y).
Proof.
by rewrite inner_metric_normE euclidean_norm_one !ffunE real_line_metric_distanceE /euclidean_one_project -opprB normrN.
Qed.

(** Source for [euclidean_real_plane_pair]: supporting usual
    identification of the Cartesian pair (x,y)
    with a point of R^2 in 2.10.29, p. 194. *)
Definition euclidean_real_plane_pair (x y : real_line_metric R) : E 2 :=
  euclidean_block_join (euclidean_one_embed x,euclidean_one_embed y).

(** Source for [euclidean_real_plane_first]: supporting first
    scalar coordinate in 2.10.29, p. 194. *)
Definition euclidean_real_plane_first (p : E 2) : real_line_metric R :=
  euclidean_one_project (@euclidean_block_split R 1 1 p).1.

(** Source for [euclidean_real_plane_second]: supporting second
    scalar coordinate in 2.10.29, p. 194. *)
Definition euclidean_real_plane_second (p : E 2) : real_line_metric R :=
  euclidean_one_project (@euclidean_block_split R 1 1 p).2.

(** Source for [euclidean_real_plane_is_metric_product]: supporting
    actual Euclidean realisation of the two
    nonexpanding scalar projections in 2.10.29,
    p. 194. All inverse laws are proved
    from the existing coordinate interfaces. *)
Theorem euclidean_real_plane_is_metric_product :
  is_metric_cartesian_product euclidean_real_plane_pair euclidean_real_plane_first euclidean_real_plane_second.
Proof.
constructor.
- move=> x y; by rewrite /euclidean_real_plane_first /euclidean_real_plane_pair euclidean_block_joinK euclidean_one_embedK.
- move=> x y; by rewrite /euclidean_real_plane_second /euclidean_real_plane_pair euclidean_block_joinK euclidean_one_embedK.
- move=> p; rewrite /euclidean_real_plane_pair /euclidean_real_plane_first /euclidean_real_plane_second
    !euclidean_one_projectK; exact (@euclidean_block_splitK R 1 1 p).
- split; first exact: ler01.
  move=> p q _ _; rewrite mul1r /euclidean_real_plane_first -euclidean_one_project_distance.
  have hh := (metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R 1 1)).2 p q Logic.I Logic.I.
  by rewrite mul1r in hh.
- split; first exact: ler01.
  move=> p q _ _; rewrite mul1r /euclidean_real_plane_second -euclidean_one_project_distance.
  have hh := (metric_product_second_nonexpanding (@euclidean_blocks_are_metric_product R 1 1)).2 p q Logic.I Logic.I.
  by rewrite mul1r in hh.
Qed.

(** Source for [euclidean_real_plane_squared_distance]: supporting
    Pythagorean diameter computation for the equal
    interval squares in 2.10.29, p. 193.
    This identity records more geometry than
    nonexpanding projections alone. *)
Lemma euclidean_real_plane_squared_distance (p q : E 2) :
  mdist p q^+2=`|euclidean_real_plane_first p-euclidean_real_plane_first q|^+2+
    `|euclidean_real_plane_second p-euclidean_real_plane_second q|^+2.
Proof.
by rewrite (@euclidean_block_squared_distance R 1 1) !euclidean_one_project_distance
  !real_line_metric_distanceE.
Qed.
End Plane.
