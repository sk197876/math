(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP ExtendedRealConventions ExtendedRealBounds
  MeasureDerivationContext MetricClosedBalls NullBallLocus CenteredBallRatioDomain
  CenteredRatioBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [fivefold_ball_ratio_values]: direct small-radius
    values for the limsup in the first alternative of Federer
    2.9.15, p. 160. Ordinary partial division excludes zero
    denominators. Radius cutoffs are finite positive reals. *)
Definition fivefold_ball_ratio_values (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) (d : R) : set (\bar R) :=
  [set y | exists r : R, (0<r)%R /\ (r<d)%R /\
    extended_divide (phi (metric_closed_ball x (5*r)%R)) (phi (metric_closed_ball x r))=Some y].

(** Source for [fivefold_ball_ratio_upper_limit]: direct radius limsup in
    Federer 2.9.15, p. 160, expressed through the sealed extended-real
    infimum and supremum. Empty value ranges have supremum negative
    infinity, consistently with 2.1.1. *)
Definition fivefold_ball_ratio_upper_limit (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) :=
  extended_real_inf [set b | exists d : R, (0<d)%R /\
    b=extended_real_sup (fivefold_ball_ratio_values phi x d)].

(** Source for [fivefold_ball_upper_limit_lt_iff]: supporting
    cutoff form of the growth limsup in Federer 2.9.15,
    p. 160. It is the strict infimum criterion for the
    small-radius suprema, including empty quotient ranges. *)
Lemma fivefold_ball_upper_limit_lt_iff (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) (b : \bar R) :
  fivefold_ball_ratio_upper_limit phi x<b <-> exists d : R,
    (0<d)%R /\ extended_real_sup (fivefold_ball_ratio_values phi x d)<b.
Proof.
split.
- move=> hl; apply: contrapT=> hn.
  have hb : b<=fivefold_ball_ratio_upper_limit phi x.
    apply: extended_real_inf_greatest=> z [d [hd ->]].
    rewrite leNgt; apply/negP=> hz; apply: hn; by exists d.
  by have := le_lt_trans hb hl; rewrite ltxx.
- move=> [d [hd hb]]; apply: le_lt_trans _ hb; apply: extended_real_inf_lower.
  by exists d.
Qed.

(** Source for [finite_upper_limit_positive_cutoff]: supporting
    finite lambda selection in Federer 2.9.15, p. 160,
    first proof case. Any extended real less than infinity
    lies strictly below a finite real lambda greater than one.
    This is order infrastructure, not a separate book theorem. *)
Lemma finite_upper_limit_positive_cutoff (R : realType) (a : \bar R) :
  a< +oo -> exists lambda : R, (1<lambda)%R /\ a<lambda%:E.
Proof.
case: a=> [a| |] ha; first last.
- exists 2%R; split; [by rewrite ltr1n|exact: ltNyr].
- by move: ha; rewrite ltxx.
exists (Num.max a 1+1)%R.
have haM : (a<=Num.max a 1)%R by rewrite le_max lexx.
have h1M : (1<=Num.max a 1)%R by rewrite le_max lexx orbT.
split; last rewrite lte_fin; by lra.
Qed.

(** Source for [fivefold_ball_growth_cutoff]: supporting
    local uniform growth estimate in Federer 2.9.15, p. 160.
    Outside P all positive-radius ratios are actual partial
    values, so the strict limsup cutoff multiplies by a positive
    finite denominator to bound the enlarged ball's mass. *)
Lemma fivefold_ball_growth_cutoff (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) (lambda : R) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  fivefold_ball_ratio_upper_limit phi x<lambda%:E -> exists d : R,
    (0<d)%R /\ forall r : R, (0<r)%R -> (r<d)%R ->
      phi (metric_closed_ball x (5*r)%R)<lambda%:E*phi (metric_closed_ball x r).
Proof.
move=> hphi hn hlim.
have [d [hd hb]] := (fivefold_ball_upper_limit_lt_iff phi x lambda%:E).1 hlim.
exists d; split=> // r hr hrd.
pose psi := fun _ : set X => phi (metric_closed_ball x (5*r)%R).
have hq := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
have hval : fivefold_ball_ratio_values phi x d
    (phi (metric_closed_ball x (5*r)%R)/phi (metric_closed_ball x r)).
  exists r; split=> //; split=> //; exact hq.
have hlt := le_lt_trans (extended_real_sup_upper hval) hb.
by rewrite -(@positive_ball_ratio_sublevel R X psi phi x r lambda hphi hn hr).
Qed.

(** Source for [finite_fivefold_ball_growth_cutoff]: direct
    local finite-cutoff consequence of the first alternative
    in Federer 2.9.15, p. 160. The positive lambda and
    radius cutoffs are supplied pointwise before the countable
    uniform-target reduction; no global doubling constant is added. *)
Lemma finite_fivefold_ball_growth_cutoff (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  fivefold_ball_ratio_upper_limit phi x< +oo -> exists (lambda d : R),
    (1<lambda)%R /\ (0<d)%R /\ forall r : R, (0<r)%R -> (r<d)%R ->
      phi (metric_closed_ball x (5*r)%R)<lambda%:E*phi (metric_closed_ball x r).
Proof.
move=> hphi hn hlim; have [lambda [hl hcut]] := finite_upper_limit_positive_cutoff hlim.
have [d [hd hb]] := @fivefold_ball_growth_cutoff R X phi x lambda hphi hn hcut.
by exists lambda,d; split=> //; split.
Qed.
