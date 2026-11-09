(** Federer (1969), 3.3.20, p. 307: actual positive similarities of original Cartesian pieces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  MetricCartesianProductUP EuclideanCantorProduct PlanarAffineRectangleTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_affine_original_product_image]: the actual
    plane similarity maps an original Cartesian product onto the product
    of its actual scalar factor images, supporting the original piece
    identities of 3.3.20, p. 307. Arbitrary factor sets and every real
    scale are allowed in this supporting set identity. *)
Theorem planar_affine_original_product_image (R:realType) (a b r:R)
    (A B:set (real_line_metric R)):
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p) @`
    euclidean_cantor_product A B=
    euclidean_cantor_product ((fun t:R=>a+r * t) @` A) ((fun t:R=>b+r * t) @` B).
Proof.
apply/seteqP;split=>z.
- move=>[p [hp0 hp1] <-];split.
  + rewrite planar_affine_first_coordinate;by exists (euclidean_real_plane_first p).
  + rewrite planar_affine_second_coordinate;by exists (euclidean_real_plane_second p).
- move=>[[x hx hX] [y hy hY]].
  exists (euclidean_real_plane_pair x y).
  + split;by rewrite
      ?(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      ?(metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  + rewrite -(metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R) z).
    rewrite -(metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R)
      (euclidean_real_plane_pair a b+r*:euclidean_real_plane_pair x y)).
    congr (euclidean_real_plane_pair _ _).
    * by rewrite planar_affine_first_coordinate (metric_product_first_pair (@euclidean_real_plane_is_metric_product R)).
    * by rewrite planar_affine_second_coordinate (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
Qed.
