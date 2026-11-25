(** Federer (1969), 3.2.16, p. 253:
    convert zero m-density to the small r^m-mass
    bounds used for the corrected annular selection.
    The normalization alpha(m) is positive finite;
    the original measure is otherwise arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction
  MetricClosedBalls MetricDensities MetricDensityNumericalBounds MetricDensityZero EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_zero_density_small_power_mass]:
    the choice of delta_i with phi(B(a,r) minus S_i)
    at most r^m 2^(-i), Federer 3.2.16,
    p. 253. The bound holds also at the
    selected positive endpoint radius. *)
Theorem metric_zero_density_small_power_mass (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A : set X) a :
  is_measure mu ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0 ->
  forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall r : R, (0<r<=d)%R ->
      mu (A `&` metric_closed_ball a r)<=(e*r^+m)%R%:E.
Proof.
move=> hm hA e he.
pose nu := measure_restrict mu A.
have hn := measure_restrict_is_measure hm A.
pose alpha := euclidean_unit_ball_volume R m.
have ha : (0<alpha)%R := (euclidean_unit_ball_volumeE R m).2.
have hc : (0<e/alpha)%R by rewrite divr_gt0.
have hu := (@metric_density_zero_iff_upper_zero R X m nu a hn).1 hA.
have [s [hs hsmall]] := (@metric_upper_density_zero_iff_small R X m nu a hn).1 hu _ hc.
exists (s/2)%R; split; first by rewrite divr_gt0 // ltr0n.
move=> r /andP [hr hrs].
have hrlt : (r<s)%R by lra.
have hrad : (0<r<s)%R by apply/andP; split.
have hmass := @metric_ball_density_value_bound R X m nu a r (e/alpha)%R hr (hsmall r hrad).
have hEq : ((e/alpha)*(alpha*r^+m)=e*r^+m)%R.
  by rewrite mulrA divfK ?gt_eqF //.
by rewrite hEq in hmass.
Qed.

(** Source for [small_power_mass_metric_zero_density]:
    the reverse small-mass implication used after
    the annular cover in Federer 3.2.16,
    p. 253. Infinite original ball mass is
    permitted; only the exceptional set is bounded. *)
Theorem small_power_mass_metric_zero_density (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A : set X) a :
  is_measure mu ->
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall r : R, (0<r<d)%R ->
      mu (A `&` metric_closed_ball a r)<=(e*r^+m)%R%:E) ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0.
Proof.
move=> hm hsmall.
pose nu := measure_restrict mu A.
have hn := measure_restrict_is_measure hm A.
pose alpha := euclidean_unit_ball_volume R m.
have ha : (0<alpha)%R := (euclidean_unit_ball_volumeE R m).2.
apply: (@metric_density_zero_iff_upper_zero R X m nu a hn).2.
apply: (@metric_upper_density_zero_iff_small R X m nu a hn).2=> e he.
have hc : (0<e*alpha)%R := mulr_gt0 he ha.
have [d [hd hs]] := hsmall _ hc.
exists d; split=> // r hr.
have hmass := hs r hr.
have hEq : ((e*alpha)*r^+m=e*(alpha*r^+m))%R by rewrite mulrA.
rewrite hEq in hmass.
rewrite leNgt; apply/negP=> hlarge.
have hlow := @metric_ball_density_value_large R X m nu a r e (andP hr).1 hlarge.
have hbad := lt_le_trans hlow hmass; by rewrite ltxx in hbad.
Qed.

(** Source for [null_set_metric_density_zero]: the
    null-point and null-set exceptional cases in
    Federer 3.2.16, p. 253. They have
    zero metric m-density at every point, without
    a measurability assumption. *)
Lemma null_set_metric_density_zero (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A : set X) a :
  is_measure mu -> mu A=0 ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0.
Proof.
move=> hm hA.
apply: (small_power_mass_metric_zero_density hm _)=> e he.
exists 1%R; split; first exact: ltr01.
move=> r /andP [hr _].
have hz : mu (A `&` metric_closed_ball a r)=0.
  apply: (@measure_null_subset R X mu hm _ A _ hA)=> x hx; exact: hx.1.
rewrite hz lee_fin; exact: mulr_ge0 (ltW he) (exprn_ge0 m (ltW hr)).
Qed.
