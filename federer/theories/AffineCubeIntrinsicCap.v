(** Federer (1969), 3.2.38, p. 275: actual uniform lower
    intrinsic-volume coefficients of the affine good-cube image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanAffineImageGeometry
  CompactConvexRadiusIntrinsicBound IntegralGeometricGauge ProjectionBeta EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_coordinate_cube_intrinsic_cap]: supporting the
    j<m coefficient bound in Federer 3.2.38, p. 275. The actual
    image of a side-h source cube lies in the ball about g(a) of
    radius L m h. Actual projection averages give a finite uniform
    coefficient depending only on n,m,L,j. This radius bound is
    weaker than the printed isodiametric constant but gives the same
    xi/v conclusion. Its valid j=0 term is retained explicitly. *)
Lemma affine_coordinate_cube_intrinsic_cap (R:realType) m n j (hjn:(j<=n)%N)
    (corner a:R_n R m) (b:R_n R n) (h L:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m)))
    (D:Hom (R_n R m) (R_n R n)):
  is_euclidean_coordinate_cube corner h Q ->Q a ->0<=L ->
  (forall v,inner_norm (@euclidean_inner_productP R n) (D v)<=
    L*inner_norm (@euclidean_inner_productP R m) v) ->
  (@integral_geometric_gauge R n j hjn 1 ((fun x=>(b+D (x-a))%R) @` Q)<=
    ((@projection_beta R n j hjn 1)^-1*euclidean_unit_ball_volume R j*(L* m%:R)^+j*h^+j)%R%:E)%E.
Proof.
move=>hQ ha hL hD.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose g:X->Y:=fun x=>b+D (x-a).
pose c:Y:=b-D a.
have hFunction:g=(fun x:X=>c+D x).
  apply:funext=>x; by rewrite /g /c linearB addrAC addrA.
have hCompact:compact (g @` Q).
  rewrite hFunction; exact:(@euclidean_affine_hom_compact_image R m n D c Q (coordinate_cube_compact hQ)).
have hConvex:is_inner_convex (g @` Q).
  rewrite hFunction; exact:(@affine_hom_convex_image R (R_n R m) (R_n R n) D c Q (coordinate_cube_convex hQ)).
have hNonempty:g @` Q!=set0 by exists (g a); exists a.
have hRadiusNonnegative:0<=L* m%:R*h.
  exact:mulr_ge0 (mulr_ge0 hL (ler0n R m)) hQ.1.
have hRadius y:(g @` Q) y ->@mdist R (inner_metric_space (@euclidean_inner_productP R n)) b y<=L* m%:R*h.
  move=>[x hx <-]; rewrite /g inner_metric_distanceE opprD addrA subrr add0r inner_normN.
  have hDistance:=coordinate_cube_distance_bound hQ hx ha.
  rewrite inner_metric_distanceE in hDistance.
  apply:le_trans (hD (x-a)) _.
  have hScaled:=ler_wpM2l hL hDistance; by rewrite mulrA in hScaled.
have hCap:=@compact_convex_radius_intrinsic_bound R n j hjn (g @` Q) b (L* m%:R*h)
  hCompact hNonempty hConvex hRadiusNonnegative hRadius.
by rewrite exprMn !mulrA in hCap.
Qed.
