(** Federer (1969), 3.3.20, pp. 307–308: actual rectangular similarities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane
  PlanePairNormGeometry MetricCartesianProductUP CompactIntervalGauge EuclideanIntervalRectangles
  AffineIntervalTransportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_affine_first_coordinate]: supporting actual
    first coordinate of the similarities in 3.3.20, pp. 307–308. *)
Lemma planar_affine_first_coordinate (R:realType) (a b r:R)
    (p:inner_metric_space (@euclidean_inner_productP R 2)):
  euclidean_real_plane_first (euclidean_real_plane_pair a b+r*:p)=a+r * euclidean_real_plane_first p.
Proof.
rewrite !real_plane_first_coordinateE.
rewrite [((euclidean_real_plane_pair a b+r*:p) ord0)]ffunE
  [((r*:p) ord0)]ffunE real_plane_pair_first_coordinate.
by rewrite /GRing.scale /=.
Qed.

(** Source for [planar_affine_second_coordinate]: supporting actual
    second coordinate of the similarities in 3.3.20, pp. 307–308. *)
Lemma planar_affine_second_coordinate (R:realType) (a b r:R)
    (p:inner_metric_space (@euclidean_inner_productP R 2)):
  euclidean_real_plane_second (euclidean_real_plane_pair a b+r*:p)=b+r * euclidean_real_plane_second p.
Proof.
rewrite !real_plane_second_coordinateE.
rewrite [((euclidean_real_plane_pair a b+r*:p) ord_max)]ffunE
  [((r*:p) ord_max)]ffunE real_plane_pair_second_coordinate.
by rewrite /GRing.scale /=.
Qed.

(** Source for [planar_positive_affine_rectangle_transport]: exact
    images of the original squares in 3.3.20, pp. 307–308. The
    scalar interval-image laws prove the actual plane set image;
    no hit-count or measure-scaling premise is assumed. *)
Theorem planar_positive_affine_rectangle_transport (R:realType) (a b r:R) M N
    (S T:compact_real_intervals R):
  is_affine_interval_transport a r M ->is_affine_interval_transport b r N ->
  euclidean_interval_rectangle (M S) (N T)=
    (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      euclidean_real_plane_pair a b+r*:p) @` euclidean_interval_rectangle S T.
Proof.
move=>hM hN;apply/seteqP;split=>z.
- move=>[hz0 hz1];rewrite hM in hz0;rewrite hN in hz1.
  have [x hx hX]:=hz0;have [y hy hY]:=hz1.
  exists (euclidean_real_plane_pair x y).
  + split;by rewrite ?(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      ?(metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  + rewrite -(metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R) z).
    rewrite -(metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R)
      (euclidean_real_plane_pair a b+r*:euclidean_real_plane_pair x y)).
    congr (euclidean_real_plane_pair _ _).
     *  by rewrite planar_affine_first_coordinate (metric_product_first_pair (@euclidean_real_plane_is_metric_product R)).
     *  by rewrite planar_affine_second_coordinate (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
- move=>[p [hp0 hp1] <-];split.
  + rewrite hM planar_affine_first_coordinate;by exists (euclidean_real_plane_first p).
  + rewrite hN planar_affine_second_coordinate;by exists (euclidean_real_plane_second p).
Qed.
