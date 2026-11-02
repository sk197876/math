(** Consequences of the abstract covering infimum in Federer (1969), 2.10.1,
    p. 170. These arguments use only the specification, without unfolding
    its implementation. Source context: MetricScaleEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MetricDiameter MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope_nonnegative]: the costs
    have nonnegative numerical sums in the infimum defining
    the approximating measure, Federer 2.10.1, p. 170. *)
Lemma metric_scale_envelope_nonnegative (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu -> forall A, 0<=nu A.
Proof.
move=> hn A; apply: (metric_scale_envelope_greatest hn)=> G _ _ _.
exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [metric_scale_envelope_unique]: uniqueness of
    the infimum in Federer 2.10.1, p. 170. *)
Lemma metric_scale_envelope_unique (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu xi : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu ->
  is_metric_scale_envelope S cost delta xi -> forall A, nu A=xi A.
Proof.
move=> hn hx A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (metric_scale_envelope_greatest hx)=> G hc hd hcov.
  exact (@metric_scale_envelope_lower R X J S cost delta nu hn A G hc hd hcov).
- apply: (metric_scale_envelope_greatest hn)=> G hc hd hcov.
  exact (@metric_scale_envelope_lower R X J S cost delta xi hx A G hc hd hcov).
Qed.

(** Source for [metric_scale_envelope_mono]: enlarging the
    set to be covered increases the infimum in Federer
    2.10.1, p. 170. *)
Lemma metric_scale_envelope_mono (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu ->
  forall A B, A `<=` B -> nu A<=nu B.
Proof.
move=> hn A B hAB; apply: (metric_scale_envelope_greatest hn)=> G hc hd hcov.
apply: (@metric_scale_envelope_lower R X J S cost delta nu hn A G hc hd)=> x hx; exact: hcov (hAB x hx).
Qed.

(** Source for [metric_scale_envelope_antitone_cutoff]: the displayed
    comparison of approximating measures in Federer 2.10.1, p. 170 Smaller
    admissible diameters increase the infimum. *)
Lemma metric_scale_envelope_antitone_cutoff (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta eta : \bar R) (nu xi : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu ->
  is_metric_scale_envelope S cost eta xi ->
  delta<=eta -> forall A, xi A<=nu A.
Proof.
move=> hn hx hde A; apply: (metric_scale_envelope_greatest hn)=> G hc hd hcov.
apply: (@metric_scale_envelope_lower R X J S cost eta xi hx A G hc _ hcov)=> j hj.
exact: le_trans (hd j hj) hde.
Qed.
