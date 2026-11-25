(** Federer (1969), 3.3.20, pp. 308–309:
    diagonal separation in every original corner orientation. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [planar_absolute_coordinate_distance_bound]:
    the sum of the absolute original coordinate gaps
    is at most sqrt(2) times actual Euclidean distance.
    This proves all diagonal orientations of the opposite-
    corner estimates in 3.3.20, pp. 308–309. *)
Lemma planar_absolute_coordinate_distance_bound (R:realType)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  `|euclidean_real_plane_first p-euclidean_real_plane_first q|+
    `|euclidean_real_plane_second p-euclidean_real_plane_second q|<=Num.sqrt 2 * mdist p q.
Proof.
pose x:=`|euclidean_real_plane_first p-euclidean_real_plane_first q|.
pose y:=`|euclidean_real_plane_second p-euclidean_real_plane_second q|.
have hSquare:=@euclidean_real_plane_squared_distance R p q.
change (mdist p q^+2=x^+2+y^+2) in hSquare.
have hRoot:Num.sqrt (2:R)^+2= 2 by rewrite sqr_sqrtr // ler0n.
have hRoot0:0<=Num.sqrt (2:R) by exact:sqrtr_ge0.
have hDistance0:0<=mdist p q by exact:mdist_ge0.
have hProduct0:0<=Num.sqrt (2:R) * mdist p q:=mulr_ge0 hRoot0 hDistance0.
have hProductSquare:(Num.sqrt (2:R) * mdist p q)^+2= 2 * (x^+2+y^+2).
  by rewrite exprMn hRoot hSquare.
have hDifference:0<=(x-y)^+2 by exact:sqr_ge0.
change (is_true (x+y<=Num.sqrt 2 * mdist p q));nra.
Qed.

(** Source for [planar_diagonal_distance_lower]: an
    original absolute-coordinate gap budget gives the actual
    Euclidean lower distance required in the finite square
    certificates of 3.3.20, pp. 308–309. Both
    diagonal orientations and arbitrary signed lower bounds
    remain; no distance estimate is assumed in a
    numbered measure theorem. *)
Lemma planar_diagonal_distance_lower (R:realType)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)) (g:R):
  Num.sqrt 2 * g<=`|euclidean_real_plane_first p-euclidean_real_plane_first q|+
    `|euclidean_real_plane_second p-euclidean_real_plane_second q| ->g<=mdist p q.
Proof.
move=>hGap.
have hRoot:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
have h:=le_trans hGap (planar_absolute_coordinate_distance_bound p q).
by move:h;rewrite ler_pM2l.
Qed.
