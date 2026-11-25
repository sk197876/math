(** Federer (1969), 2.9.19, pp. 163–164: V consists of compact nondegenerate
    real intervals containing the base point and is a Lebesgue Vitali
    relation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls ScalarLebesgueBallContext
  NoncenteredBallRelations LebesgueScalarMeasure MeasureDerivationContext CoveringRelationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_nondegenerate_interval_relation]: direct V in Federer
    2.9.19, p. 163: the compact nondegenerate interval [a,b] contains x.
    Endpoints are finite real numbers and a<b is strict. *)
Definition scalar_nondegenerate_interval_relation (R : realType)
    (x : real_line_metric R) (S : set (real_line_metric R)) :=
  exists a b : R, a<b /\ S=`[a,b] /\ a<=x<=b.

(** Source for [scalar_interval_noncentered_ball_iff]: supporting equality
    of the interval V in Federer 2.9.19, p. 163, with the noncentered-ball
    V. Center (a+b)/2 and radius (b-a)/2 give one direction; the ball
    endpoints a-r,a+r give the other. *)
Lemma scalar_interval_noncentered_ball_iff (R : realType)
    (x : real_line_metric R) (S : set (real_line_metric R)) :
  scalar_nondegenerate_interval_relation x S <-> noncentered_closed_ball_relation x S.
Proof.
split.
- move=> [a [b [hab [-> hx]]]].
  pose c : real_line_metric R := (a+b)/2.
  pose r := (b-a)/2.
  have hr : 0<r by rewrite /r; lra.
  have he : metric_closed_ball c r=`[a,b].
    rewrite scalar_metric_closed_ball_interval.
    have hl : c-r=a by rewrite /c /r; lra.
    have hu : c+r=b by rewrite /c /r; lra.
    by rewrite hl hu.
  exists c,r; split; first exact hr.
  split; first exact: esym he.
  by rewrite /= in_itv.
- move=> [a [r [hr [-> hx]]]].
  exists (a-r),(a+r); split; first by lra.
  split; first exact: scalar_metric_closed_ball_interval.
  by move: hx; rewrite scalar_metric_closed_ball_interval /= in_itv.
Qed.

(** Source for [scalar_interval_relation_eq_balls]: supporting relation
    equality reconciling Federer 2.9.19, p. 163. It identifies the same
    intervals and base points; it does not alter which sets occur in the
    Vitali relation. *)
Lemma scalar_interval_relation_eq_balls (R : realType) :
  @scalar_nondegenerate_interval_relation R=
    @noncentered_closed_ball_relation R [the metricType R of real_line_metric R].
Proof.
apply: funext=> x; apply: funext=> S; apply: propext.
exact: scalar_interval_noncentered_ball_iff.
Qed.

(** Source for [scalar_nondegenerate_intervals_vitali]: direct opening
    observation in the proof of Federer 2.9.19, p. 164. The established
    fivefold interval-growth argument applies through the exact relation
    equality, without changing the printed intervals. *)
Lemma scalar_nondegenerate_intervals_vitali (R : realType) :
  @is_vitali_relation R [the metricType R of real_line_metric R]
    (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R).
Proof.
rewrite scalar_interval_relation_eq_balls.
exact: scalar_lebesgue_noncentered_balls_vitali.
Qed.

(** Source for [scalar_interval_derivation_context]: supporting standing
    reference/Vitali context for Federer 2.9.19, pp. 163–164 Scalar Lebesgue
    measure has the original class-M bounded-set finiteness property, in
    addition to the printed nondegenerate-interval Vitali relation. *)
Lemma scalar_interval_derivation_context (R : realType) :
  @is_measure_derivation_context R [the metricType R of real_line_metric R]
    (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R).
Proof.
constructor; [exact: scalar_lebesgue_derivation_class|exact: scalar_nondegenerate_intervals_vitali].
Qed.
