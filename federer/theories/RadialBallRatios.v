(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureDerivates
  MeasureDerivationContext MetricClosedBalls NullBallLocus CenteredBallRatioDomain CenteredRatioBorel
  ExtendedRealBounds FivefoldBallGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_ball_ratio_values]: direct small-radius
    quotient values for the limsup in Federer 2.9.17,
    p. 162. Positive-radius ball quotients retain their actual
    partial domains; no zero-denominator value is inserted. *)
Definition centered_ball_ratio_values (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (d : R) : set (\bar R) :=
  [set y | exists r : R, (0<r)%R /\ (r<d)%R /\
    partial_function_graph (measure_ratio_function psi phi) (metric_closed_ball x r) y].

(** Source for [centered_ball_ratio_upper_limit]: direct radial
    limsup in Federer 2.9.17, p. 162, expressed by
    the existing sealed extended infimum and supremum. The
    statement's growth assumption will prove denominator positivity;
    this definition itself preserves partial quotient conventions. *)
Definition centered_ball_ratio_upper_limit (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :=
  extended_real_inf [set b | exists d : R, (0<d)%R /\
    b=extended_real_sup (centered_ball_ratio_values psi phi x d)].

(** Source for [centered_ball_ratio_upper_limit_lt_iff]: supporting
    radius-cutoff criterion for the finite upper limit in
    Federer 2.9.17, p. 162, preceding the closed
    sets C_n. This is an order consequence of the abstract
    infimum laws, without numerator regularity assumptions. *)
Lemma centered_ball_ratio_upper_limit_lt_iff (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (c : \bar R) :
  centered_ball_ratio_upper_limit psi phi x<c <-> exists d : R,
    (0<d)%R /\ extended_real_sup (centered_ball_ratio_values psi phi x d)<c.
Proof.
split.
- move=> hl; apply: contrapT=> hn.
  have hb : c<=centered_ball_ratio_upper_limit psi phi x.
    apply: extended_real_inf_greatest=> b [d [hd ->]].
    rewrite leNgt; apply/negP=> h; apply: hn; by exists d.
  by have := le_lt_trans hb hl; rewrite ltxx.
- move=> [d [hd hb]]; apply: le_lt_trans _ hb; apply: extended_real_inf_lower.
  by exists d.
Qed.

(** Source for [finite_centered_ball_ratio_cutoff]: supporting
    finite-coefficient radius bound used to form C_n in
    Federer 2.9.17, p. 162. Outside the null-ball
    locus every positive-radius denominator is finite positive,
    and a finite upper ratio limit bounds all small-ball masses.
    The numerator may be an arbitrary set function here. *)
Lemma finite_centered_ball_ratio_cutoff (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  centered_ball_ratio_upper_limit psi phi x< +oo -> exists c d : R,
    (1<c)%R /\ (0<d)%R /\ forall r : R, (0<r)%R -> (r<d)%R ->
      psi (metric_closed_ball x r)<c%:E*phi (metric_closed_ball x r).
Proof.
move=> hphi hn hlim.
have [c [hc hcut]] := finite_upper_limit_positive_cutoff hlim.
have [d [hd hsup]] := (centered_ball_ratio_upper_limit_lt_iff psi phi x c%:E).1 hcut.
exists c,d; split=> //; split=> // r hr hrd.
have hq := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
have hv : centered_ball_ratio_values psi phi x d
    (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)).
  by exists r; split=> //; split.
have hlt := le_lt_trans (extended_real_sup_upper hv) hsup.
by rewrite -(@positive_ball_ratio_sublevel R X psi phi x r c hphi hn hr).
Qed.
