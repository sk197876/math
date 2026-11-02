(** Federer (1969), 2.9.18(1), p. 163: real-line Lebesgue measure and
    closed-ball ratios in the first sharpness example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricBoundedUnion
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureDerivationContext LebesgueScalarMeasure
  NoncenteredBallRelations NoncenteredDoublingVitali CoveringRelationUP
  UniformBallGrowthAdequacy NullBallLocus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_metric_closed_ball_interval]: direct
    real-line closed balls used in Federer 2.9.18(1),
    p. 163. The absolute-distance ball B(a,r) is
    the closed interval [a-r,a+r], including radius zero. *)
Lemma scalar_metric_closed_ball_interval (R : realType) (a : real_line_metric R) (r : R) :
  metric_closed_ball a r=`[a-r,a+r].
Proof.
apply/seteqP; split=> x; rewrite /metric_closed_ball /= real_line_metric_distanceE
  ler_norml in_itv /= => /andP [h1 h2]; apply/andP; split; lra.
Qed.

(** Source for [scalar_lebesgue_closed_ball]: direct denominator
    L^1 B(x,r)=2r in Federer 2.9.18(1), p. 163,
    from the segment-length law of 2.5.17. The degenerate
    radius-zero ball also has the stated zero measure. *)
Lemma scalar_lebesgue_closed_ball (R : realType) (a : real_line_metric R) (r : R) :
  0<=r -> lebesgue_scalar_measure (metric_closed_ball a r)=(2*r)%:E.
Proof.
move=> hr; rewrite scalar_metric_closed_ball_interval lebesgue_scalar_segment; last by lra.
congr (_%:E); lra.
Qed.

(** Source for [scalar_lebesgue_derivation_class]: supporting
    standing class M for the reference in Federer 2.9.18(1),
    p. 163. Borel regularity is already proved, and
    every bounded set lies in a finite scalar interval. *)
Lemma scalar_lebesgue_derivation_class (R : realType) :
  @is_derivation_measure R [the metricType R of real_line_metric R] (@lebesgue_scalar_measure R).
Proof.
constructor.
- exact: lebesgue_scalar_is_measure.
- exact: lebesgue_scalar_borel_regular.
- move=> A hA.
  have [r [hr hdist]] := @metric_bounded_distance_bound R
    [the metricType R of real_line_metric R] A 0 hA.
  have hsub : A `<=` `[-r,r].
    move=> x hx; have h := hdist x hx.
    rewrite real_line_metric_distanceE sub0r normrN in h.
    by rewrite /= in_itv /= -ler_norml.
  apply: le_lt_trans (@measure_mono R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) A `[-r,r] hsub) _.
  rewrite lebesgue_scalar_segment; first exact: ltry.
  lra.
Qed.

(** Source for [scalar_lebesgue_noncentered_balls_vitali]: supporting
    standing Vitali relation for applying 2.9.17 in Federer
    2.9.18(1), p. 163. The proof uses the
    positive-ball fivefold-growth criterion of 2.9.16 and the
    exact interval-length formula, with no separability assumption. *)
Lemma scalar_lebesgue_noncentered_balls_vitali (R : realType) :
  @is_vitali_relation R [the metricType R of real_line_metric R] (@lebesgue_scalar_measure R)
    (@noncentered_closed_ball_relation R [the metricType R of real_line_metric R]).
Proof.
apply: (@doubling_noncentered_balls_vitali R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) 5 (scalar_lebesgue_derivation_class R)
  (ltac:(by rewrite ler0n))).
- move=> a r hr; rewrite scalar_lebesgue_closed_ball ?ltW // lte_fin mulr_gt0 // ltr0n.
- move=> a r hr.
  have h5 : 0<5*r by rewrite mulr_gt0 // ltr0n.
  rewrite (@scalar_lebesgue_closed_ball R a (5*r) (ltW h5))
    (@scalar_lebesgue_closed_ball R a r (ltW hr)) -EFinM lee_fin.
  lra.
Qed.

(** Source for [scalar_lebesgue_countable_null]: supporting
    nullity of a countable dense set in the construction of
    the positive nowhere dense compact target for Federer
    2.9.18(1), p. 163. Singleton lengths vanish,
    and countable unions of null sets are null. *)
Lemma scalar_lebesgue_countable_null (R : realType) (D : set (real_line_metric R)) :
  countable D -> lebesgue_scalar_measure D=0%E.
Proof.
move=> hD.
have he : D=\bigcup_(x in D) [set x].
  apply/seteqP; split=> x; first by move=> hx; exists x.
  by move=> [y hy ->].
rewrite he; apply: (@measure_null_countable_union R R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) D (fun x => [set x]) hD).
by move=> x _; exact: lebesgue_scalar_singleton.
Qed.


(** Source for [scalar_lebesgue_positive_ball]: supporting
    positive denominator masses for the ratios in Federer
    2.9.18(1), p. 163. Every positive-radius
    scalar ball has positive length 2r. *)
Lemma scalar_lebesgue_positive_ball (R : realType) (x : real_line_metric R) (r : R) :
  0<r -> (0<lebesgue_scalar_measure (metric_closed_ball x r))%E.
Proof.
move=> hr; rewrite (@scalar_lebesgue_closed_ball R x r (ltW hr)) lte_fin.
by rewrite mulr_gt0 // ltr0n.
Qed.

(** Source for [scalar_lebesgue_no_null_ball_points]: supporting
    absence of undefined small ball ratios in Federer
    2.9.18(1), p. 163. The scalar Lebesgue
    reference has no point with a positive-radius null ball. *)
Lemma scalar_lebesgue_no_null_ball_points (R : realType) (x : real_line_metric R) :
  ~ @measure_null_ball_points R [the metricType R of real_line_metric R] (@lebesgue_scalar_measure R) x.
Proof.
move=> [r [hr hz]]; have hp := @scalar_lebesgue_positive_ball R x r hr.
by rewrite hz ltxx in hp.
Qed.

(** Source for [scalar_lebesgue_uniform_fivefold_growth]: supporting
    application of 2.9.17 in Federer 2.9.18(1), p. 163.
    Scalar fivefold growth is exactly five; finite coefficient
    six gives the required strict inequality at every positive
    radius and hence at any chosen radius cutoff. *)
Lemma scalar_lebesgue_uniform_fivefold_growth (R : realType) (mu : R) :
  @has_uniform_fivefold_ball_growth R [the metricType R of real_line_metric R]
    (@lebesgue_scalar_measure R) setT mu 6.
Proof.
move=> x _ r hr _.
have h5 : 0<5*r by rewrite mulr_gt0 // ltr0n.
rewrite (@scalar_lebesgue_closed_ball R x (5*r) (ltW h5))
  (@scalar_lebesgue_closed_ball R x r (ltW hr)) -EFinM lte_fin.
lra.
Qed.
