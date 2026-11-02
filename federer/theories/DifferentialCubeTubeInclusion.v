(** Federer (1969), 3.2.38, p. 274: actual affine comparison
    on a good source cube, before applying the full Steiner polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry MetricOpenThickening MetricImageTubeApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [differential_coordinate_cube_tube_inclusion]: the
    affine-map tube inclusion at the end of Federer 3.2.38, p. 274.
    A good point a lies in the actual cube of side h, so its
    actual first-order error is at most e m h. The derivative is
    an auxiliary local witness; no selected field or global regularity
    of that field is assumed. All natural source dimensions remain. *)
Lemma differential_coordinate_cube_tube_inclusion (R:realType) m n
    (b a:R_n R m) (h e r:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m)))
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (D:Hom (R_n R m) (R_n R n)):
  is_euclidean_coordinate_cube b h Q ->Q a ->0<=e ->
  (forall x,Q x ->inner_norm (@euclidean_inner_productP R n) (f x-f a-D (x-a))<=
    e*inner_norm (@euclidean_inner_productP R m) (x-a)) ->
  metric_open_thickening (f @` Q) r `<=`
    metric_open_thickening ((fun x=>f a+D (x-a)) @` Q) (r+e* m%:R*h).
Proof.
move=>hQ ha he hRemainder.
apply:metric_pointwise_image_tube_inclusion=>x hx.
rewrite inner_metric_distanceE opprD addrA.
have hBound:=hRemainder x hx.
have hDistance:=coordinate_cube_distance_bound hQ hx ha.
rewrite inner_metric_distanceE in hDistance.
apply:le_trans hBound _.
have hScaled:=ler_wpM2l he hDistance.
by rewrite mulrA in hScaled.
Qed.
