(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext PartialFunctionUP
  MetricClosedBalls CoveringFamilyLaws NullBallLocus CenteredBallRatioDomain CenteredRatioBorel
  ClosedBallRatioBounds RadialBallRatios ExtendedRealBounds ExtendedRealReciprocalBounds
  RealLatticeTruncationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [natural_centered_ball_ratio_locus]: direct
    countable coefficient/radius loci in C_n of Federer
    2.9.17, p. 162. Index n=0 denotes printed
    positive integer 1, so the coefficient is n+1 and
    the radius cutoff its reciprocal. *)
Definition natural_centered_ball_ratio_locus (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (n : nat) :=
  bounded_centered_ball_ratio_locus psi phi (n.+1)%:R (((n.+1)%:R)^-1)%R.

(** Source for [finite_centered_ball_ratio_natural_cutoff]:
    supporting cofinality step in the displayed union of C_n
    in Federer 2.9.17, p. 162. Increase one
    positive integer to bound the finite ratio coefficient and
    make its reciprocal smaller than the available radius cutoff. *)
Lemma finite_centered_ball_ratio_natural_cutoff (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  centered_ball_ratio_upper_limit psi phi x< +oo ->
  exists n, natural_centered_ball_ratio_locus psi phi n x.
Proof.
move=> hphi hn hfinite.
have [c [d [hc [hd hbound]]]] := @finite_centered_ball_ratio_cutoff R X psi phi x hphi hn hfinite.
have hc0 : (0<c)%R := lt_trans ltr01 hc.
pose N := Num.bound c.
have hcN : (c<N%:R)%R := archi_boundP (ltW hc0).
have [M hM] := positive_reciprocal_nat_small hd.
pose n := maxn N M.
have hcnext : (c<((n.+1)%:R : R))%R.
  apply: lt_le_trans hcN _; rewrite ler_nat; exact: leq_trans (leq_maxl N M) (leqnSn n).
have hradius : ((((n.+1)%:R : R)^-1)<d)%R.
  exact: le_lt_trans (@positive_reciprocal_nat_antitone R M n (leq_maxr N M)) hM.
exists n=> r hr hrcap.
have hrd : (r<d)%R := lt_trans hrcap hradius.
apply: le_trans (ltW (hbound r hr hrd)) _.
apply: (@lee_wpmul2r R (phi (metric_closed_ball x r))
  (@measure_nonnegative R X phi (derivation_measure_law hphi) _) _ _).
by rewrite lee_fin; exact: ltW hcnext.
Qed.

(** Source for [bounded_centered_ball_ratio_finite_upper_limit]:
    supporting converse in the union of C_n in Federer
    2.9.17, p. 162. A finite mass coefficient
    on a positive radius interval bounds the actual ratio
    limsup, because every denominator there is positive finite. *)
Lemma bounded_centered_ball_ratio_finite_upper_limit (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (c d : R) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x -> (0<d)%R ->
  bounded_centered_ball_ratio_locus psi phi c d x ->
  centered_ball_ratio_upper_limit psi phi x< +oo.
Proof.
move=> hphi hn hd hb; have hm := derivation_measure_law hphi.
have hlev : centered_ball_ratio_upper_limit psi phi x<=
    extended_real_sup (centered_ball_ratio_values psi phi x d).
  apply: extended_real_inf_lower; by exists d.
apply: le_lt_trans hlev _; apply: le_lt_trans _ (@ltry R (c+1)%R).
apply: extended_real_sup_least=> y [r [hr [hrd hy]]].
have hq := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
have hey := partial_function_single_valued hy hq; rewrite hey; apply: ltW.
rewrite (@positive_ball_ratio_sublevel R X psi phi x r (c+1)%R hphi hn hr).
apply: le_lt_trans (hb r hr hrd) _.
have hp := @outside_null_ball_points_positive R X phi x r hm hn hr.
have hf : phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact (@derivation_measure_bounded_finite R X phi hphi _
    (@covering_closed_ball_bounded R X x r (ltW hr))).
pose m := fine (phi (metric_closed_ball x r)).
have he : phi (metric_closed_ball x r)=m%:E by rewrite /m fineK.
have hmp : (0<m)%R by move: hp; rewrite he lte_fin.
by rewrite he -!EFinM lte_fin (ltr_pM2r hmp) ltrDl ltr01.
Qed.

(** Source for [finite_centered_ball_ratio_natural_cover]: direct
    displayed countable union of uniform loci in Federer
    2.9.17, p. 162, before intersecting the
    closed target. The exclusion of null-ball points is
    later proved from the theorem's strict growth hypothesis. *)
Lemma finite_centered_ball_ratio_natural_cover (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  (centered_ball_ratio_upper_limit psi phi x< +oo <->
    exists n, natural_centered_ball_ratio_locus psi phi n x).
Proof.
move=> hphi hn; split; first exact: finite_centered_ball_ratio_natural_cutoff hphi hn.
move=> [n hnloc].
exact (@bounded_centered_ball_ratio_finite_upper_limit R X psi phi x
  (n.+1)%:R (((n.+1)%:R)^-1)%R hphi hn
  (ltac:(by rewrite invr_gt0 ltr0n)) hnloc).
Qed.
