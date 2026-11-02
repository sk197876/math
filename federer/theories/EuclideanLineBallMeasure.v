(** Federer (1969), 2.9.18(2), p. 163: the straight-line reference measure
    on Euclidean space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanCoordinateMetric EuclideanAffineLineMeasure MetricClosedBalls
  ScalarLebesgueBallContext LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_affine_line_centered_ball_measure]: direct
    line mass phi B(x,r)=2r for x on T in Federer
    2.9.18(2), p. 163. The coordinate-line
    parametrisation is an isometry, so its inverse image of
    the ambient closed ball is the scalar interval ball.
    The result holds in every dimension with a coordinate line. *)
Lemma euclidean_affine_line_centered_ball_measure (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (s r : R) : 0<=r ->
  euclidean_affine_line_measure i v (metric_closed_ball (euclidean_coordinate_line i v s) r)=(2*r)%:E.
Proof.
move=> hr; rewrite euclidean_affine_line_measure_preimage.
have he : (euclidean_coordinate_line i v) @^-1`
    metric_closed_ball (euclidean_coordinate_line i v s) r=metric_closed_ball (s : real_line_metric R) r.
  by apply/seteqP; split=> t; rewrite /metric_closed_ball /= euclidean_coordinate_line_distance.
by rewrite he scalar_lebesgue_closed_ball.
Qed.
