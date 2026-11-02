(** Federer (1969), 2.9.18(2), p. 163: the constant quotient one at every
    positive radius. This order lemma turns an actual constant quotient
    graph into its radial upper limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls PartialFunctionUP MeasureDerivates RadialBallRatios
  RadialBallLowerLimit ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [constant_centered_ball_ratio_upper_limit]:
    supporting radial limit calculation in Federer 2.9.18(2),
    p. 163. If every positive-radius quotient is
    actually defined and equals q, each small-radius value
    range is the singleton q, so its upper limit is q. *)
Lemma constant_centered_ball_ratio_upper_limit (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (q : \bar R) :
  (forall r : R, (0<r)%R ->
    partial_function_graph (measure_ratio_function psi phi) (metric_closed_ball x r) q) ->
  centered_ball_ratio_upper_limit psi phi x=q.
Proof.
move=> hq; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: le_trans _ (ltac:(exact: lexx q)).
  apply: le_trans (@extended_real_inf_lower R _
    (extended_real_sup (centered_ball_ratio_values psi phi x 1%R)) _ ) _.
  + exists 1%R; split=> //; exact: ltr01.
  + apply: extended_real_sup_least=> y [r [hr [_ hy]]].
    have he : y=q := partial_function_single_valued hy (hq r hr).
    by rewrite he.
- apply: centered_ball_ratio_upper_bound_from_cofinal_value=> d hd.
  have hp : (0<d/2)%R by rewrite divr_gt0 // ltr0n.
  exists (d/2)%R; split; last exact (hq (d/2)%R hp).
  apply/andP; split; lra.
Qed.
