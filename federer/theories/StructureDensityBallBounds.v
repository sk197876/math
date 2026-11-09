(** Federer (1969), 3.3.4, p. 291:
    actual density one gives finite positive
    two-sided reference ball estimates at every
    sufficiently small positive real radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDensities MetricDensityNumericalBounds
  MetricClosedBalls PositiveRightOrderLimit EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_density_one_ball_bounds]:
    supporting the reference-denominator replacement in
    Federer 3.3.4, p. 291. At all sufficiently
    small positive radii the original ball mass
    lies strictly above half its Euclidean
    normalization and below twice that normalization.
    Degree zero and all intermediate radii remain. *)
Lemma structure_density_one_ball_bounds (R:realType) (X:metricType R)
    m (mu:set X->\bar R) (a:X):
  positive_right_extended_order_limit (metric_ball_density m mu a) 1%E ->
  exists d:R,0<d /\ forall r,0<r<d ->
    (((euclidean_unit_ball_volume R m/2)*r^+m)%:E<mu (metric_closed_ball a r))%E /\
    (mu (metric_closed_ball a r)<=((2*euclidean_unit_ball_volume R m)*r^+m)%:E)%E.
Proof.
move=>hLimit.
have hHalfE:(((2:R)^-1)%:E<1%E)%E.
  by rewrite lte_fin invf_lt1 ?ltr0n // ltr1n.
have hTwoE:(1%E<(2:R)%:E)%E by rewrite lte_fin ltr1n.
have [dL [hdL hLower]]:=hLimit.1 _ hHalfE.
have [dU [hdU hUpper]]:=hLimit.2 _ hTwoE.
exists (Num.min dL dU); split; first by rewrite lt_min hdL hdU.
move=>r /andP [hr hrd].
have /andP [hrL hrU]:(r<dL) && (r<dU) by move:hrd; rewrite lt_min.
split.
- have h:=metric_ball_density_value_large hr (hLower r hr hrL).
  by rewrite mulrCA mulrA in h.
- have h:=metric_ball_density_value_bound hr (ltW (hUpper r hr hrU)).
  by rewrite mulrA in h.
Qed.
