(** Federer (1969), 2.9.18(2), p. 163: exact ball ratios for the line
    reference and projected off-line outer measure. its diameter denominator
    differs from the present reference-ball denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateMetric EuclideanAffineLineMeasure EuclideanLineBallMeasure
  OffLineProjectionMeasure MetricClosedBalls MeasureUP MeasureBasic MeasureDerivationContext
  MeasureDerivates PartialFunctionUP NullBallLocus CenteredBallRatioDomain
  RadialBallRatios ConstantRadialBallRatio UniformBallGrowthAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Ratios.
Variable R : realType.
Variable n : nat.
Variable i j : 'I_n.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation phi := (euclidean_affine_line_measure i v).
Local Notation psi := (off_line_projection_measure i v).

(** Source for [line_reference_positive_centered_ball]:
    supporting positive denominator in Federer 2.9.18(2),
    p. 163, at a point of T. Its value
    2r is strictly positive for every positive radius. *)
Lemma line_reference_positive_centered_ball (s r : R) : 0<r ->
  (0<phi (metric_closed_ball (f s) r))%E.
Proof.
move=> hr; rewrite euclidean_affine_line_centered_ball_measure ?ltW // lte_fin.
by rewrite mulr_gt0 // ltr0n.
Qed.

(** Source for [line_reference_no_null_ball_on_line]:
    supporting definedness of all quotients at x in T
    in Federer 2.9.18(2), p. 163. No claim
    of support positivity at points outside T is made. *)
Lemma line_reference_no_null_ball_on_line (s : R) :
  ~measure_null_ball_points phi (f s).
Proof.
move=> [r [hr hz]]; have hp := line_reference_positive_centered_ball s hr.
by rewrite hz ltxx in hp.
Qed.

(** Source for [line_projection_centered_ball_ratio]: direct
    psi B(x,r)/phi B(x,r)= 1 in Federer 2.9.18(2),
    p. 163, for x in T and positive r.
    Both masses are computed before division; the denominator
    is positive finite and its partial quotient is defined. *)
Lemma line_projection_centered_ball_ratio (s r : R) : j != i -> 0<r ->
  partial_function_graph (measure_ratio_function psi phi)
    (metric_closed_ball (f s) r) 1%E.
Proof.
move=> hji hr.
have hq := @centered_ball_ratio_positive_domain R E phi psi (f s) r
  (euclidean_affine_line_measure_class i v) (@line_reference_no_null_ball_on_line s) hr.
have h2r : 0<2*r by rewrite mulr_gt0 // ltr0n.
have hn : 2*r != 0 by rewrite (gt_eqF h2r).
have he : (psi (metric_closed_ball (f s) r)/phi (metric_closed_ball (f s) r))%E= 1%E.
  rewrite (@off_line_projection_ball_measure R n i j v s r hji hr)
    (@euclidean_affine_line_centered_ball_measure R n i v s r (ltW hr)) inver (gt_eqF h2r) -EFinM.
  by rewrite divff.
by rewrite he in hq.
Qed.

(** Source for [line_reference_fivefold_ball_ratio]: direct
    phi B(x,5r)/phi B(x,r)= 5 in Federer 2.9.18(2),
    p. 163. Exact interval lengths prove the quotient
    at every point on T and every positive radius. *)
Lemma line_reference_fivefold_ball_ratio (s r : R) : 0<r ->
  (phi (metric_closed_ball (f s) (5*r))/phi (metric_closed_ball (f s) r))%E= 5%E.
Proof.
move=> hr.
have h5 : 0<5*r by rewrite mulr_gt0 // ltr0n.
have h2r : 0<2*r by rewrite mulr_gt0 // ltr0n.
have hn : 2*r != 0 by rewrite (gt_eqF h2r).
rewrite (@euclidean_affine_line_centered_ball_measure R n i v s (5*r) (ltW h5))
  (@euclidean_affine_line_centered_ball_measure R n i v s r (ltW hr)) inver (gt_eqF h2r) -EFinM.
congr (_%:E).
apply: (mulIf hn); rewrite divfK //; ring.
Qed.

(** Source for [line_projection_upper_ball_ratio_one]: direct
    finite positive upper limit in the second counterexample
    of Federer 2.9.18, p. 163. All actual
    positive-radius quotients are one, so the literal upper
    radial ratio is one at every point on T. *)
Lemma line_projection_upper_ball_ratio_one (s : R) : j != i ->
  centered_ball_ratio_upper_limit psi phi (f s)= 1%E.
Proof.
move=> hji; apply: constant_centered_ball_ratio_upper_limit=> r hr.
exact (@line_projection_centered_ball_ratio s r hji hr).
Qed.
End Ratios.
