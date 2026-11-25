(** Federer (1969), 3.1.2, pp. 211–212: approximate limits use Lebesgue
    measure and positive-radius closed balls centered at the base point.
    The Vitali property is inherited from the already proved ball theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanNoncenteredVitali ScalarLebesgueBallContext RealMetricBackground
  LebesgueScalarMeasure CenteredBallRelations NoncenteredBallRelations
  CoveringRelationUP CoveringRelationFineness MeasureDerivationContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_centered_balls_vitali]: the Vitali relation V
    specified in Federer 3.1.2, p. 212, first display. Every natural
    dimension is retained; centered balls form an everywhere-fine subrelation. *)
Theorem euclidean_centered_balls_vitali (R : realType) n :
  is_vitali_relation (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]).
Proof.
apply: (vitali_fine_subrelation (euclidean_noncentered_balls_vitali R n)).
- exact: centered_closed_balls_subrelation.
- exact: centered_closed_balls_fine.
Qed.

(** Source for [euclidean_approximate_context]: Federer 3.1.2, p. 212,
    the pair used to abbreviate the approximate limits of 2.9.12. *)
Lemma euclidean_approximate_context (R : realType) n :
  is_measure_derivation_context (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]).
Proof.
constructor; [exact: euclidean_lebesgue_derivation_class|
  exact: euclidean_centered_balls_vitali].
Qed.

(** Source for [scalar_approximate_context]: Federer 3.1.2, p. 212,
    last display: approximate partial derivatives use one-dimensional
    Lebesgue measure on the scalar increment variable. *)
Lemma scalar_approximate_context (R : realType) :
  @is_measure_derivation_context R [the metricType R of real_line_metric R]
    (@lebesgue_scalar_measure R)
    (@centered_closed_ball_relation R [the metricType R of real_line_metric R]).
Proof.
constructor; first exact: scalar_lebesgue_derivation_class.
apply: (vitali_fine_subrelation (scalar_lebesgue_noncentered_balls_vitali R)).
- exact: centered_closed_balls_subrelation.
- exact: centered_closed_balls_fine.
Qed.
