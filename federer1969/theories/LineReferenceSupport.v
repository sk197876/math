(** Federer (1969), 2.9.18(2), p. 163: the growth inequality holds on the
    supporting line and fails globally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanCoordinateMetric
  EuclideanPlaneLines EuclideanAffineLineGeometry EuclideanAffineLineMeasure EuclideanLineBallMeasure
  RealMetricBackground LebesgueScalarMeasure MetricClosedBalls MeasureUP MeasureBasic MeasureRestriction
  MeasureDerivationContext UniformBallGrowthAdequacy StrictFivefoldGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Support.
Variable R : realType.
Variable n : nat.
Variable i j : 'I_n.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation T := (euclidean_affine_coordinate_line i v).
Local Notation phi := (euclidean_affine_line_measure i v).

(** Source for [line_reference_complement_null]: direct
    phi(X minus T)=0 in Federer 2.9.18(2), p. 163.
    The reference is Hausdorff length restricted to T. *)
Lemma line_reference_complement_null : phi (~` T)=0%E.
Proof.
rewrite euclidean_affine_line_measure_preimage.
have he : f @^-1` (~` T)=set0.
  apply/seteqP; split=> t; last by move=> [].
  by move=> hn; apply: hn; exists t.
by rewrite he; exact: measure_empty (lebesgue_scalar_is_measure R).
Qed.

(** Source for [line_reference_growth_on_support]: direct
    fivefold growth on T in Federer 2.9.18(2), p. 163.
    The exact ratio five gives the strict inequality with
    coefficient six, for every positive radius cutoff.
    The null complement makes this a reference-almost-
    everywhere growth hypothesis on the whole ambient space. *)
Lemma line_reference_growth_on_support (mu : R) :
  has_uniform_fivefold_ball_growth phi T mu 6.
Proof.
move=> x [s _ <-] r hr _.
have h5 : 0<5*r by rewrite mulr_gt0 // ltr0n.
rewrite (@euclidean_affine_line_centered_ball_measure R n i v s (5*r) (ltW h5))
  (@euclidean_affine_line_centered_ball_measure R n i v s r (ltW hr)) -EFinM lte_fin.
lra.
Qed.

(** Source for [line_reference_off_support_null_ball]: supporting
    failure of the everywhere growth hypothesis in Federer
    2.9.18(2), p. 163. Moving one unit in
    a second coordinate produces a closed radius-one-half
    ball disjoint from the supporting line. The scalar
    coordinate distance is a lower bound for Euclidean distance. *)
Lemma line_reference_off_support_null_ball : j != i ->
  phi (metric_closed_ball (euclidean_coordinate_line j v 1) (1/2))=0%E.
Proof.
move=> hji; rewrite euclidean_affine_line_measure_preimage.
have he : f @^-1` metric_closed_ball (euclidean_coordinate_line j v 1) (1/2)=set0.
  apply/seteqP; split=> s; last by move=> [].
  move=> hs.
  have hbound := le_trans (@euclidean_coordinate_nonexpanding R n j
    (euclidean_coordinate_line j v 1) (f s)) hs.
  rewrite real_line_metric_distanceE !euclidean_coordinate_line_value eqxx
    (negbTE hji) mulr1 mulr0 addr0 addrAC subrr add0r normr1 in hbound.
  have hstrict : (1/2 : R)<1 by lra.
  by have hbad := lt_le_trans hstrict hbound; rewrite ltxx in hbad.
by rewrite he; exact: measure_empty (lebesgue_scalar_is_measure R).
Qed.

(** Source for [line_reference_growth_not_global]: direct
    necessity of an everywhere rather than almost-everywhere
    growth hypothesis in Federer 2.9.18(2), p. 163.
    Global strict growth would force every positive-radius
    ball to have positive mass, contradicting the explicit
    off-support null ball. Every finite coefficient and every
    positive cutoff are excluded. *)
Lemma line_reference_growth_not_global (lambda mu : R) : j != i -> 0<mu ->
  ~has_uniform_fivefold_ball_growth phi setT mu lambda.
Proof.
move=> hji hmu hg.
have hp := @strict_fivefold_growth_ball_positive R E phi lambda mu
  (derivation_measure_law (euclidean_affine_line_measure_class i v)) hmu hg
  (euclidean_coordinate_line j v 1) (1/2) (ltac:(by rewrite divr_gt0 // ltr0n)).
by rewrite (line_reference_off_support_null_ball hji) ltxx in hp.
Qed.
End Support.
