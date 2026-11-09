(** Federer (1969), 3.3.20, p. 307: scalar projection commutes with original similarities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane PlanarAffineRectangleTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_scalar_original_similarity_projection]: the
    actual projection of each original square piece is a translated
    r-scaled copy of the unit projection, supporting the projection
    partitions in 3.3.20, p. 307. No projection measure or overlap
    conclusion is assumed. *)
Theorem planar_scalar_original_similarity_projection (R:realType) (a b r u v:R)
    (C:set (inner_metric_space (@euclidean_inner_productP R 2))):
  let P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p in
  P @` ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_real_plane_pair a b+r*:p) @` C)=
    (fun t:R=>u * a+v * b+r * t) @` (P @` C).
Proof.
move=>P;rewrite !image_comp;apply:congr1.
apply:funext=>p;rewrite /P /= planar_affine_first_coordinate planar_affine_second_coordinate;ring.
Qed.
