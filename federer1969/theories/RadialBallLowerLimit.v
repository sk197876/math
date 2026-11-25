(** Federer (1969), 2.9.18(1), p. 163: lower and upper radial quotient
    bounds in the oscillating example. The lower limit is specified through
    sealed order bounds over actual partial quotient graph values. These
    order lemmas support the printed lower limit zero and upper bound
    one-half. The measure-formula erratum issue is treated separately in
    ErratumWeightedHitCounterexample.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureDerivates DerivationRatioDomain PartialFunctionUP
  RadialBallRatios MetricClosedBalls ExtendedRealBounds ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [centered_ball_ratio_lower_limit]: direct lower
    positive-radius ball-ratio limit in Federer 2.9.18(1),
    p. 163. It is the supremum over positive
    cutoffs of the infima of actual quotient graph values,
    dual to the upper ratio limit used in 2.9.17. *)
Definition centered_ball_ratio_lower_limit (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :=
  extended_real_sup [set b | exists d : R, (0<d)%R /\
    b=extended_real_inf (centered_ball_ratio_values psi phi x d)].

(** Source for [centered_ball_ratio_lower_limit_nonnegative]:
    supporting sign of the lower ratio limit in Federer
    2.9.18(1), p. 163. Every actual measure
    quotient is nonnegative; empty value ranges have infimum
    positive infinity and do not invalidate this lower bound. *)
Lemma centered_ball_ratio_lower_limit_nonnegative (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_measure psi -> is_measure phi -> 0<=centered_ball_ratio_lower_limit psi phi x.
Proof.
move=> hpsi hphi.
have hlev : extended_real_inf (centered_ball_ratio_values psi phi x 1%R)<=
    centered_ball_ratio_lower_limit psi phi x.
  apply: extended_real_sup_upper; exists 1%R; split=> //; exact: ltr01.
apply: le_trans _ hlev; apply: extended_real_inf_greatest=> y [r [_ [_ hy]]].
exact (@measure_ratio_nonnegative R X psi phi (metric_closed_ball x r) y hpsi hphi hy).
Qed.

(** Source for [centered_ball_ratio_lower_limit_zero]: supporting
    small-value criterion for the lower limit in Federer
    2.9.18(1), p. 163. An actual quotient
    below every positive epsilon occurs below every positive
    radius cutoff; together with nonnegativity this forces zero. *)
Lemma centered_ball_ratio_lower_limit_zero (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_measure psi -> is_measure phi ->
  (forall d e : R, (0<d)%R -> (0<e)%R -> exists r y,
    (0<r<d)%R /\
    partial_function_graph (measure_ratio_function psi phi) (metric_closed_ball x r) y /\ y<e%:E) ->
  centered_ball_ratio_lower_limit psi phi x=0.
Proof.
move=> hpsi hphi hs; apply/eqP.
rewrite eq_le (@centered_ball_ratio_lower_limit_nonnegative R X psi phi x hpsi hphi) andbT.
apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=> n; rewrite add0r.
have hp : (0<(((n.+1)%:R : R)^-1))%R by rewrite invr_gt0 ltr0n.
apply: extended_real_sup_least=> b [d [hd ->]].
have [r [y [hr [hy hsmall]]]] := hs d _ hd hp.
apply: le_trans _ (ltW hsmall); apply: extended_real_inf_lower.
exists r; split; first exact: (andP hr).1.
by split; [exact: (andP hr).2|].
Qed.

(** Source for [centered_ball_ratio_upper_bound_from_cofinal_value]:
    supporting upper-limit bound 1/2 in Federer 2.9.18(1),
    p. 163. If every radius cutoff contains
    an actual quotient value q, then the upper radial
    ratio is at least q. No totalised quotient is used. *)
Lemma centered_ball_ratio_upper_bound_from_cofinal_value (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (q : \bar R) :
  (forall d : R, (0<d)%R -> exists r, (0<r<d)%R /\
    partial_function_graph (measure_ratio_function psi phi) (metric_closed_ball x r) q) ->
  q<=centered_ball_ratio_upper_limit psi phi x.
Proof.
move=> hs; apply: extended_real_inf_greatest=> b [d [hd ->]].
have [r [/andP [hr hrd] hq]] := hs d hd.
apply: extended_real_sup_upper; by exists r; split=> //; split.
Qed.
