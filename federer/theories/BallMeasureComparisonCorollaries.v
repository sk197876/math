(** Federer (1969), 2.9.14, pp. 159–160: openness of the locus where one
    closed-ball measure strictly exceeds another for an allowed radius. The
    proof uses monotonicity, continuity from above in 2.1.3(5), p. 55, and
    the metric triangle inequality. no separate item there states this
    ball-comparison lemma. The working erratum has no correction to 2.9.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricClosedBalls MeasureUP
  MeasureDerivationContext OpenBallMeasureComparison ScaledDerivationMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [ball_measure_upper_comparison_open]: direct
    first corollary of Federer 2.9.14, p. 160. Psi is
    any measure, phi belongs to the standing class M, t is
    finite positive, and J is an open positive-radius set. *)
Corollary ball_measure_upper_comparison_open (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (J : set (real_line_metric R)) (t : R) :
  is_derivation_measure phi -> is_measure psi -> (0<t)%R -> open J ->
  (forall r, J r -> (0<r)%R) ->
  open [set x | exists r : R, J r /\ t%:E*phi (metric_closed_ball x r)<psi (metric_closed_ball x r)].
Proof.
move=> hphi hpsi ht hJ hpos.
exact: (@federer_2_9_14 R X psi (fun S => t%:E*phi S) J hpsi
  (@positive_scaled_derivation_measure R X phi t hphi ht) hJ hpos).
Qed.

(** Source for [ball_measure_lower_comparison_open]: direct
    second corollary of Federer 2.9.14, p. 160. Both
    measures belong to M, as phi does throughout 2.9; in
    particular psi's bounded finiteness is required in this
    orientation. Apply the theorem with numerator t phi. *)
Corollary ball_measure_lower_comparison_open (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (J : set (real_line_metric R)) (t : R) :
  is_derivation_measure phi -> is_derivation_measure psi -> (0<t)%R -> open J ->
  (forall r, J r -> (0<r)%R) ->
  open [set x | exists r : R, J r /\ psi (metric_closed_ball x r)<t%:E*phi (metric_closed_ball x r)].
Proof.
move=> hphi hpsi ht hJ hpos.
have hscale := @positive_scaled_derivation_measure R X phi t hphi ht.
exact: (@federer_2_9_14 R X (fun S => t%:E*phi S) psi J
  (derivation_measure_law hscale) hpsi hJ hpos).
Qed.
