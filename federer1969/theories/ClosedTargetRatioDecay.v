(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext MeasureDerivates
  MeasureRestriction PartialFunctionUP MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricSetDistanceUP DistanceBallRatioBound StrictFivefoldGrowth UniformBallGrowthAdequacy
  ClosedBallRatioBounds CenteredBallRelations CenteredBallRatioDomain CoveringRelationLimits
  CoveringFiniteLimitBounds NullBallLocus RadialRatioZero RadialBallRatios.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [closed_target_ratio_decay]: direct pointwise
    density step at the end of the proof of Federer
    2.9.17, p. 162. If the complement of A
    has centered density zero at x in A, the covering
    estimate bounds the numerator ratio by c lambda^3 times
    that complement density at radius 2r. This gives an
    arbitrarily small positive bound and hence zero upper radial
    derivative. The numerator has only measure laws. *)
Theorem closed_target_ratio_decay (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (A : set X) (d : X -> R)
    (hd : is_metric_set_distance A d) (c delta lambda mu : R) (x : X) :
  is_derivation_measure phi -> is_measure psi -> closed A -> (0<=c)%R -> (0<lambda)%R ->
  (0<delta)%R -> (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  (forall z, A z -> bounded_centered_ball_ratio_locus psi phi c delta z) ->
  psi A=0 -> A x ->
  partial_function_graph (measure_derivate (measure_restrict phi (~` A)) phi
    (@centered_closed_ball_relation R X)) x 0 ->
  centered_ball_ratio_upper_limit psi phi x=0.
Proof.
move=> hphi hpsi hA hc hl hdelta hmu hg hbound hnull hx hD.
have hm := derivation_measure_law hphi.
have hn := @strict_fivefold_growth_no_null_balls R X phi lambda mu hm hmu hg x.
apply: (@centered_ball_ratio_upper_limit_zero R X psi phi x hphi hpsi hn)=> e he.
pose K := (c*lambda^+3)%R.
have hK : (0<=K)%R by rewrite /K mulr_ge0 // exprn_ge0 //; exact: ltW hl.
have hK1 : (0<K+1)%R by lra.
pose alpha := (e/(K+1))%R.
have halpha : (0<alpha)%R by rewrite /alpha divr_gt0.
have [b [hb hsmall]] := @covering_finite_limit_small_values R X
  (@centered_closed_ball_relation R X)
  (measure_ratio_function (measure_restrict phi (~` A)) phi) x 0%R alpha hD halpha.
pose cap := (Num.min (delta/4) (Num.min (mu/4) (b/5)))%R.
have hcap : (0<cap)%R.
  rewrite /cap !lt_min; repeat (apply/andP; split); rewrite ?divr_gt0 ?ltr0n //.
exists cap; split=> // r hr hrcap.
have hrd : (r<delta/4)%R.
  apply: lt_le_trans hrcap _; by rewrite /cap ge_min lexx.
have hrmu : (r<mu/4)%R.
  apply: lt_le_trans hrcap _; rewrite /cap ge_min; apply/orP; right.
  by rewrite ge_min lexx.
have hrb : (r<b/5)%R.
  apply: lt_le_trans hrcap _; rewrite /cap ge_min; apply/orP; right.
  by rewrite ge_min lexx orbT.
have h2r : (0<2*r)%R by rewrite mulr_gt0 // ltr0n.
have hdiam : extended_metric_diameter (metric_closed_ball x (2*r)%R)<b%:E.
  have hbd : extended_metric_diameter (metric_closed_ball x (2*r)%R)<=(2*r+2*r)%R%:E.
    apply: (@metric_diameter_least R X _ _ (extended_metric_diameter_specification _)
      ((2*r+2*r)%R)%:E).
    - by rewrite lee_fin; lra.
    - move=> y z hy hz; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hy hz.
  apply: le_lt_trans hbd _; rewrite lte_fin; lra.
have hq := @centered_ball_ratio_positive_domain R X phi (measure_restrict phi (~` A)) x
  (2*r)%R hphi hn h2r.
have hV : centered_closed_ball_relation x (metric_closed_ball x (2*r)%R) by exists (2*r)%R.
have hden := (hsmall _ _ hV hdiam hq).2.
rewrite add0r in hden.
have hrestr : measure_restrict phi (~` A) (metric_closed_ball x (2*r)%R)=
    phi (metric_closed_ball x (2*r)%R `\` A) by rewrite /measure_restrict setDE setIC.
rewrite hrestr in hden.
have hbound_ratio := @distance_ball_ratio_measure_bound R X phi psi A d hd c delta lambda mu x r
  hphi hpsi hA hc hl hmu hg hbound hnull hx hr hrd hrmu.
apply: le_lt_trans hbound_ratio _.
have hscale := @lee_wpmul2l R K%:E (ltac:(by rewrite lee_fin)) _ _ (ltW hden).
have heq : ((c*lambda^+3)%R)%:E=K%:E by [].
rewrite heq; apply: le_lt_trans hscale _.
rewrite -EFinM lte_fin /alpha mulrCA -{2}(mulr1 e) (ltr_pM2l he).
by rewrite ltr_pdivrMr // mul1r ltrDl ltr01.
Qed.
