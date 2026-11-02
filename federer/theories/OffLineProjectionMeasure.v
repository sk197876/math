(** Federer (1969), 2.9.18(2), p. 163: the projected outer measure after
    removing the supporting line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra num_normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanCoordinateMetric
  EuclideanAffineLineGeometry MetricClosedBalls MeasureUP MeasureBasic ImageComplementMeasure
  OffLineBallProjection LebesgueScalarMeasure EuclideanLebesgueBoxes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [off_line_projection_measure]: direct formula
    psi(A)=L^1[p(A minus T)] in Federer 2.9.18(2),
    p. 163, for the coordinate projection x -> x_i
    and the affine coordinate line T. Real scalars identify
    the one-dimensional Euclidean target. *)
Definition off_line_projection_measure (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) :=
  image_complement_measure (@lebesgue_scalar_measure R)
    (fun x : inner_metric_space (@euclidean_inner_productP R n) => x i)
    (euclidean_affine_coordinate_line i v).

(** Source for [off_line_projection_is_measure]: direct
    assertion that psi measures Euclidean space in Federer
    2.9.18(2), p. 163. Only outer-measure laws
    are asserted; no Borel-regularity assumption is imposed. *)
Lemma off_line_projection_is_measure (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) :
  is_measure (off_line_projection_measure i v).
Proof. exact: image_complement_measure_is_measure (lebesgue_scalar_is_measure R). Qed.

(** Source for [off_line_projection_target_null]: direct
    psi(T)= 0 in Federer 2.9.18(2), p. 163.
    Removing T before taking the image gives the empty set. *)
Lemma off_line_projection_target_null (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) :
  off_line_projection_measure i v (euclidean_affine_coordinate_line i v)= 0%E.
Proof. exact: image_complement_measure_target_null (lebesgue_scalar_is_measure R). Qed.

(** Source for [off_line_projection_ball_measure]: direct
    numerator psi B(x,r)= 2r for x on T in Federer
    2.9.18(2), p. 163. The projected punctured
    ball lies between open and closed intervals of the same
    length. A second coordinate is necessary; no result
    for a one-dimensional ambient line is claimed. *)
Lemma off_line_projection_ball_measure (R : realType) n (i j : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (s r : R) :
  j != i -> 0<r -> off_line_projection_measure i v
    (metric_closed_ball (euclidean_coordinate_line i v s) r)=(2*r)%:E.
Proof.
move=> hji hr; pose a := euclidean_coordinate_line i v s i.
have hab : a-r<=a+r by lra.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (le_trans (@measure_mono R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ (@off_line_ball_projection_upper R n i v s r))).
  rewrite lebesgue_scalar_segment // lee_fin /a; lra.
- have hlow := @measure_mono R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ (@off_line_ball_projection_lower R n i j v s r hji).
  rewrite lebesgue_scalar_open_interval in hlow; last exact hab.
  have he : a+r-(a-r)= 2*r by lra.
  by rewrite -/a he in hlow.
Qed.
