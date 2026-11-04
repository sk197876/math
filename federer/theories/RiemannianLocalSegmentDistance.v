(** Federer (1969), 3.2.46, p. 281: the straight
    segment proves rho(x,y) <= lambda |L(x-y)| in the
    local frozen comparison region. The integral and
    admissibility assertions have already been proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RealMetricBackground EuclideanEllipsoidSegment
  RiemannianTensorUP RiemannianAffineSegmentUpper RiemannianCurveCost
  RiemannianDistanceUP RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_local_segment_distance_upper]:
    the actual local upper distance bound in Federer 3.2.46,
    p. 281, from an actual segment and its tensor-speed integral.
    The local tensor comparison is used on the entire segment. *)
Lemma riemannian_local_segment_distance_upper (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (L : {linear R_n R n -> R_n R n}) a x y r lambda :
  0 < lambda ->
  (forall z, inner_norm (@euclidean_inner_productP R n) (L (z-a)) <= r ->
    A z /\ forall v, riemannian_tensor_speed g z v <=
      lambda*inner_norm (@euclidean_inner_productP R n) (L v)) ->
  inner_norm (@euclidean_inner_productP R n) (L (x-a)) <= r ->
  inner_norm (@euclidean_inner_productP R n) (L (y-a)) <= r ->
  (@riemannian_distance R n A g x y <=
    ((lambda*inner_norm (@euclidean_inner_productP R n) (L (y-x)))%R)%:E)%E.
Proof.
move=> hLambda hControl hx hy.
have hSegment t : 0 <= t <= 1 ->
    inner_norm (@euclidean_inner_productP R n) (L ((x+t*:(y-x))-a)) <= r.
  move=> ht; exact (@euclidean_ellipsoid_segment_bound R n L a x y r t hx hy ht).
have hImage t : 0 <= t <= 1 -> A (x+t*:(y-x)).
  by move=> ht; exact: (hControl _ (hSegment t ht)).1.
have hC := riemannian_affine_segment_admissible hImage.
have hBound t : 0 <= t <= 1 ->
    riemannian_tensor_speed g (x+t*:(y-x)) (y-x) <=
      lambda*inner_norm (@euclidean_inner_productP R n) (L (y-x)).
  move=> ht; exact: (hControl _ (hSegment t ht)).2.
have hCost := riemannian_affine_segment_cost_upper hg hImage
  (mulr_ge0 (ltW hLambda) (inner_norm_nonnegative _ _)) hBound.
exact: le_trans (riemannian_distance_curve_bound (riemannian_distance_laws A g x y) hC) hCost.
Qed.
