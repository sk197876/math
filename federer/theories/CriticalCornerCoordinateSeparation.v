(** Federer (1969), 3.3.20, pp. 308–309:
    opposite-corner interval coordinates give actual distance bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import RealMetricBackground CriticalCornerCoordinate
  EuclideanInnerProduct InnerMetric EuclideanRealPlane PlanarAbsoluteCoordinateDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_opposite_corner_coordinate_gap]:
    supporting coordinate gap for original opposite corner
    intervals in 3.3.20, pp. 308–309.
    Both interval orientations are retained, and a
    negative lower bound is harmless. *)
Lemma critical_opposite_corner_coordinate_gap (R:realType) (r:R)
    (b:bool) (a c:nat) (x y:R):
  0<r ->
  (`[critical_corner_coordinate r b a,critical_corner_coordinate r b a+1/r]:set R) x ->
  (`[critical_corner_coordinate r (negb b) c,critical_corner_coordinate r (negb b) c+1/r]:set R) y ->
  1-((a+c+2)%:R:R)/r<=`|x-y|.
Proof.
move=>hr hx hy.
have hNorm: x-y<=`|x-y| by exact:ler_norm.
have hNormOpp:y-x<=`|x-y|.
  have h:y-x<=`|y-x| by exact:ler_norm.
  by rewrite distrC in h.
rewrite !natrD !mulrDl !mul1r.
case:b hx hy=>[|];rewrite /critical_corner_coordinate /= !in_itv /= !natrD !mulrDl !mul1r;
  move=>/andP[hx0 hx1] /andP[hy0 hy1];lra.
Qed.

(** Source for [critical_opposite_corner_square_gap]:
    the original inward coordinate budget B gives
    distance at least sqrt(2)(1-(B+4)/(2r)),
    for every pair of points in opposite actual
    corner squares, 3.3.20, pp. 308–309.
    This proves the printed square distance estimate
    from actual coordinates rather than assuming it. *)
Lemma critical_opposite_corner_square_gap (R:realType) (r:R)
    (b d:bool) (a c e f budget:nat)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  0<r ->(a+c+e+f<=budget)%N ->
  (`[critical_corner_coordinate r b a,critical_corner_coordinate r b a+1/r]:set R)
    (euclidean_real_plane_first p) ->
  (`[critical_corner_coordinate r d c,critical_corner_coordinate r d c+1/r]:set R)
    (euclidean_real_plane_second p) ->
  (`[critical_corner_coordinate r (negb b) e,critical_corner_coordinate r (negb b) e+1/r]:set R)
    (euclidean_real_plane_first q) ->
  (`[critical_corner_coordinate r (negb d) f,critical_corner_coordinate r (negb d) f+1/r]:set R)
    (euclidean_real_plane_second q) ->
  Num.sqrt 2 * (1-(budget+4)%:R/(2*r))<=mdist p q.
Proof.
move=>hr hBudget hp0 hp1 hq0 hq1.
have hX:=critical_opposite_corner_coordinate_gap hr hp0 hq0.
have hY:=critical_opposite_corner_coordinate_gap hr hp1 hq1.
have hBudgetR:((a+c+e+f)%:R:R)<=budget%:R by rewrite ler_nat.
rewrite !natrD in hBudgetR hX hY.
have hRoot:Num.sqrt (2:R)^+2= 2 by rewrite sqr_sqrtr // ler0n.
have hDistance:=@planar_absolute_coordinate_distance_bound R p q.
have hInverse:0<=r^-1 by rewrite invr_ge0;exact:ltW hr.
have hBudgetScaled:=ler_wpM2r hInverse hBudgetR.
have hNZ:r!=0 by rewrite gt_eqF.
have hCancel:(2*r)^-1= r^-1/2 by field;by rewrite hNZ.
have hRootPositive:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
rewrite natrD hCancel.
have hMultiply:=ler_wpM2l (ltW hRootPositive) hDistance.
rewrite mulrA -expr2 hRoot in hMultiply.
nra.
Qed.
