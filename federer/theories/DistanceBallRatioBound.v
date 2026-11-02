(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import MeasureUP MeasureBasic MeasureNullModification MeasureDerivationContext
  MetricClosedBalls CoveringFamilyLaws MetricSetDistanceUP DistanceBallCoverBound
  StrictFivefoldGrowth UniformBallGrowthAdequacy ClosedBallRatioBounds NonnegativeRatioTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [distance_ball_ratio_measure_bound]: direct
    final displayed ratio estimate in Federer 2.9.17,
    p. 162: psi B(x,r)/phi B(x,r) is at
    most c lambda^3 times the relative mass of B(x,2r)
    minus A. Numerator-nullity of A allows removing A;
    the third growth factor compares the two denominators.
    Their positivity and finiteness are proved, and no infinite
    subtraction or undefined quotient is used. The right-hand
    ball follows erratum p. 3, book p. 162 lines 24–25. *)
Theorem distance_ball_ratio_measure_bound (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (A : set X) (d : X -> R)
    (hd : is_metric_set_distance A d) (c delta lambda mu : R) (x : X) (r : R) :
  is_derivation_measure phi -> is_measure psi -> closed A -> (0<=c)%R -> (0<lambda)%R ->
  (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  (forall z, A z -> bounded_centered_ball_ratio_locus psi phi c delta z) ->
  psi A=0 -> A x -> (0<r)%R -> (r<delta/4)%R -> (r<mu/4)%R ->
  psi (metric_closed_ball x r)/phi (metric_closed_ball x r)<=
    ((c*lambda^+3)%R)%:E*
      (phi (metric_closed_ball x (2*r)%R `\` A)/phi (metric_closed_ball x (2*r)%R)).
Proof.
move=> hphi hpsi hA hc hl hmu hg hbound hnull hx hr hrd hrm.
have hm := derivation_measure_law hphi.
pose B := metric_closed_ball x r.
pose D := metric_closed_ball x (2*r)%R.
pose E := D `\` A.
pose C := (c*lambda^+2)%R.
have hC0 : (0<=C)%R by rewrite /C mulr_ge0 // sqr_ge0.
have h2r : (0<2*r)%R by rewrite mulr_gt0 // ltr0n.
have hrmu : (r<mu)%R by lra.
have hpB := @strict_fivefold_growth_ball_positive R X phi lambda mu hm hmu hg x r hr.
have hpD := @strict_fivefold_growth_ball_positive R X phi lambda mu hm hmu hg x (2*r)%R h2r.
have hfinite (t : R) (ht : (0<t)%R) : phi (metric_closed_ball x t) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact (@derivation_measure_bounded_finite R X phi hphi _ (@covering_closed_ball_bounded R X x t (ltW ht))).
have hfB := hfinite r hr.
have hfD := hfinite (2*r)%R h2r.
have hED : phi E<=phi D := @measure_mono R X phi hm E D (fun _ h => h.1).
have hfE : phi E \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm E)).
  apply: le_lt_trans hED _; by rewrite -(fineK hfD); exact: ltry.
have hremove : psi B=psi (B `\` A).
  apply: (@measure_null_modification_value R X psi hpsi B (B `\` A) A hnull).
  move=> z hn; split; first by move=> hz; split.
  by move=> [hz _].
have hmass : psi B<=C%:E*phi E.
  rewrite hremove.
  exact (@distance_ball_cover_measure_bound R X phi psi A d hd c delta lambda mu x r
    hphi hpsi hA hc hl hmu hg hbound hx hr hrd hrm).
have hfpsi : psi B \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hpsi B)).
  apply: le_lt_trans hmass _; by rewrite -(fineK hfE) -EFinM; exact: ltry.
have hsub25 : D `<=` metric_closed_ball x (5*r)%R.
  move=> z hz; apply: le_trans hz _; lra.
have hden : phi D<=lambda%:E*phi B.
  exact: le_trans (@measure_mono R X phi hm D _ hsub25) (ltW (hg x I r hr hrmu)).
pose a := fine (psi B); pose b := fine (phi B).
pose e := fine (phi E); pose q := fine (phi D).
have ha : psi B=a%:E by rewrite /a fineK.
have hb : phi B=b%:E by rewrite /b fineK.
have he : phi E=e%:E by rewrite /e fineK.
have hq : phi D=q%:E by rewrite /q fineK.
have hbp : (0<b)%R by move: hpB; rewrite hb lte_fin.
have hqp : (0<q)%R by move: hpD; rewrite hq lte_fin.
have he0 : (0<=e)%R by have := measure_nonnegative hm E; rewrite he lee_fin.
have har : (a<=C*e)%R by move: hmass; rewrite ha he -EFinM lee_fin.
have hqr : (q<=lambda*b)%R by move: hden; rewrite hq hb -EFinM lee_fin.
have htransfer := @nonnegative_two_denominator_ratio_bound R a b e q C lambda
  hbp hqp he0 hC0 har hqr.
have hcoef : (C*lambda=c*lambda^+3)%R by rewrite /C; ring.
rewrite hcoef in htransfer.
change (psi B/phi B<=((c*lambda^+3)%R)%:E*(phi E/phi D)).
by rewrite ha hb he hq !inver (gt_eqF hbp) (gt_eqF hqp) -!EFinM lee_fin.
Qed.
