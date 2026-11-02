(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext MetricClosedBalls
  PartialFunctionUP MeasureDerivates CoveringFamilyLaws CenteredBallRatioDomain UniformBallGrowthAdequacy NullBallLocus CenteredRatioBorel FivefoldBallGrowth ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [strict_fivefold_growth_ball_positive]: supporting
    positivity implicit in the strict uniform growth hypothesis
    of Federer 2.9.17, p. 162. A null small ball
    would make its fivefold mass strictly negative. Every other
    positive-radius ball contains such a small positive-mass ball.
    No separate positivity or support assumption is added. *)
Lemma strict_fivefold_growth_ball_positive (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (lambda mu : R) :
  is_measure phi -> (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  forall a r, (0<r)%R -> 0<phi (metric_closed_ball a r).
Proof.
move=> hm hmu hg a r hr.
pose q := (Num.min r (mu/2))%R.
have hq : (0<q)%R by rewrite /q lt_min hr divr_gt0 // ltr0n.
have hqr : (q<=r)%R by rewrite /q ge_min lexx.
have hqm : (q<mu)%R.
  have hb : (q<=mu/2)%R by rewrite /q ge_min lexx orbT.
  have hh : (mu/2<mu)%R by lra.
  exact: le_lt_trans hb hh.
have hne : phi (metric_closed_ball a q)!=0.
  apply/negP=> /eqP hz.
  have hb := hg a I q hq hqm.
  by rewrite hz mule0 ltNge (measure_nonnegative hm) in hb.
have hp : 0<phi (metric_closed_ball a q).
  by rewrite lt_neqAle eq_sym hne (measure_nonnegative hm).
apply: lt_le_trans hp (@measure_mono R X phi hm _ _ _).
by move=> y hy; exact: le_trans hy hqr.
Qed.

(** Source for [strict_fivefold_growth_no_null_balls]: supporting
    exclusion of undefined ball quotients in Federer 2.9.17,
    p. 162. The printed strict growth hypothesis makes the
    null-ball locus empty, even for radii larger than mu. *)
Lemma strict_fivefold_growth_no_null_balls (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (lambda mu : R) :
  is_measure phi -> (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  forall x, ~ measure_null_ball_points phi x.
Proof.
move=> hm hmu hg x [r [hr hz]].
have hp := @strict_fivefold_growth_ball_positive R X phi lambda mu hm hmu hg x r hr.
by rewrite hz ltxx in hp.
Qed.

(** Source for [strict_fivefold_growth_finite_upper_limit]: supporting
    finite growth upper limit used for the covering criterion in
    Federer 2.9.17, p. 162. The constant lambda is
    finite by its real type, and the quotient is actually
    defined at all positive radii by the preceding positivity law. *)
Lemma strict_fivefold_growth_finite_upper_limit (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (lambda mu : R) :
  is_derivation_measure phi -> (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  forall x, fivefold_ball_ratio_upper_limit phi x< +oo.
Proof.
move=> hphi hmu hg x.
have hn := @strict_fivefold_growth_no_null_balls R X phi lambda mu
  (derivation_measure_law hphi) hmu hg x.
have hlev : fivefold_ball_ratio_upper_limit phi x<=
    extended_real_sup (fivefold_ball_ratio_values phi x mu).
  apply: extended_real_inf_lower; by exists mu.
apply: le_lt_trans hlev _.
apply: le_lt_trans _ (@ltry R lambda).
apply: extended_real_sup_least=> y [r [hr [hrm hy]]].
  pose psi := fun _ : set X => phi (metric_closed_ball x (5*r)%R).
  have hactual := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
  have heq : y=phi (metric_closed_ball x (5*r)%R)/phi (metric_closed_ball x r).
    have hgraph : partial_function_graph (MeasureDerivates.measure_ratio_function psi phi)
        (metric_closed_ball x r) y := hy.
    exact: partial_function_single_valued hgraph hactual.
  rewrite heq; apply: ltW.
  rewrite (@positive_ball_ratio_sublevel R X psi phi x r lambda hphi hn hr).
  exact: hg x I r hr hrm.
Qed.

(** Source for [strict_fivefold_growth_coefficient_gt_one]: supporting
    sign of lambda in the estimates of Federer 2.9.17,
    p. 162. At any point the strict growth hypothesis
    and ball inclusion force lambda>1. The point argument
    preserves the vacuous empty-space case without adding an
    inhabited-space hypothesis to the theorem. *)
Lemma strict_fivefold_growth_coefficient_gt_one (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (lambda mu : R) :
  is_derivation_measure phi -> (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  X -> (1<lambda)%R.
Proof.
move=> hphi hmu hg x; have hm := derivation_measure_law hphi.
pose r := (mu/2)%R.
have hr : (0<r)%R by rewrite /r divr_gt0 // ltr0n.
have hrm : (r<mu)%R by rewrite /r; lra.
have hp := @strict_fivefold_growth_ball_positive R X phi lambda mu hm hmu hg x r hr.
have hfin : phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact (@derivation_measure_bounded_finite R X phi hphi _ (@covering_closed_ball_bounded R X x r (ltW hr))).
pose m := fine (phi (metric_closed_ball x r)).
have he : phi (metric_closed_ball x r)=m%:E by rewrite /m fineK.
have hmp : (0<m)%R by move: hp; rewrite he lte_fin.
have hsub : metric_closed_ball x r `<=` metric_closed_ball x (5*r)%R.
  move=> y hy; apply: le_trans hy _; lra.
have hb := le_lt_trans (@measure_mono R X phi hm _ _ hsub) (hg x I r hr hrm).
by move: hb; rewrite he -EFinM lte_fin -{1}(mul1r m) (ltr_pM2r hmp).
Qed.
