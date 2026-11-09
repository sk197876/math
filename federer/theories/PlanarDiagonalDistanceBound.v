(** Federer (1969), 3.3.20, pp. 308–309:
    diagonal coordinate bounds for actual original square pairs. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [planar_coordinate_sum_distance_bound]:
    the sum of the two signed coordinate differences
    is at most sqrt(2) times actual Euclidean distance.
    This elementary Cauchy inequality supports the four
    opposite-corner pairing estimates of 3.3.20,
    pp. 308–309, on original squares. *)
Lemma planar_coordinate_sum_distance_bound (R:realType)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  (euclidean_real_plane_first q-euclidean_real_plane_first p)+
    (euclidean_real_plane_second q-euclidean_real_plane_second p)<=Num.sqrt 2* mdist p q.
Proof.
pose x:=euclidean_real_plane_first q-euclidean_real_plane_first p.
pose y:=euclidean_real_plane_second q-euclidean_real_plane_second p.
have hSquare:=@euclidean_real_plane_squared_distance R p q.
have hAbsX:`|euclidean_real_plane_first p-euclidean_real_plane_first q|^+2=x^+2.
  have hOpp:euclidean_real_plane_first p-euclidean_real_plane_first q= -x by rewrite /x opprB.
  by rewrite real_normK ?num_real // hOpp sqrrN.
have hAbsY:`|euclidean_real_plane_second p-euclidean_real_plane_second q|^+2=y^+2.
  have hOpp:euclidean_real_plane_second p-euclidean_real_plane_second q= -y by rewrite /y opprB.
  by rewrite real_normK ?num_real // hOpp sqrrN.
rewrite hAbsX hAbsY in hSquare.
have hRoot:Num.sqrt (2:R)^+2= 2 by rewrite sqr_sqrtr // ler0n.
have hRoot0:0<=Num.sqrt (2:R) by exact:sqrtr_ge0.
have hDistance0:0<=mdist p q by exact:mdist_ge0.
have hProduct0:0<=Num.sqrt (2:R)* mdist p q:=mulr_ge0 hRoot0 hDistance0.
have hProductSquare:(Num.sqrt (2:R)* mdist p q)^+2= 2*(x^+2+y^+2).
  by rewrite exprMn hRoot hSquare.
have hDifference:0<=(x-y)^+2 by exact:sqr_ge0.
change (is_true (x+y<=Num.sqrt 2* mdist p q));nra.
Qed.
