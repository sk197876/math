(** Federer (1969), 2.9.19, p. 164: continuity points of a real function of
    locally bounded variation are dense. We derive it from the already
    proved nullity of discontinuities and positive length of every real
    ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricOpenShrinking MetricClosedBalls
  ScalarLebesgueBallContext LebesgueScalarMeasure MeasureAlmostBasic CurveArcLength
  StieltjesFiniteDerivates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_lebesgue_conull_set_dense]: supporting density
    criterion for the continuity endpoints in Federer 2.9.19, p. 164 A
    nonempty open set contains a positive-radius closed ball of positive
    length, so it cannot be contained in a null set. *)
Lemma scalar_lebesgue_conull_set_dense (R : realType) (D : set (real_line_metric R)) :
  lebesgue_scalar_measure (~` D)=0%E -> dense D.
Proof.
move=> hnull U [x hx] hU.
have [r [hr hsub]] := @metric_open_contains_closed_ball R
  [the metricType R of real_line_metric R] U x hU hx.
apply: contrapT=> hn.
have hB : lebesgue_scalar_measure (metric_closed_ball x r)=0%E.
  apply: (@measure_null_subset R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ (~` D) _ hnull).
  move=> y hy hDy; apply: hn; exists y; by split; first exact: hsub.
have hp := @scalar_lebesgue_positive_ball R x r hr.
by rewrite hB ltxx in hp.
Qed.

(** Source for [real_bv_continuity_points_dense]: direct density of
    continuity points used in Federer 2.9.19, p. 164 Countably many
    discontinuities have already been removed in real_bv_continuity_ae,
    using 2.5.16. No extra endpoint continuity is required of the original
    curve. *)
Lemma real_bv_continuity_points_dense (R : realType) (g : R -> real_line_metric R) :
  curve_locally_finite_variation g -> dense [set x | g @ x --> g x].
Proof.
move=> hg; apply: scalar_lebesgue_conull_set_dense.
exact: real_bv_continuity_ae hg.
Qed.
