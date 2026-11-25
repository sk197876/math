(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP MeasureDerivationContext
  MetricClosedBalls MetricDiameter MetricDiameterUP CoveringFamilyUP CoveringFamilyLaws
  MetricSetDistanceUP HalfDistanceBallGeometry DistanceBallMeasureBound ClosedBallRatioBounds
  StrictFivefoldGrowth UniformBallGrowthAdequacy DiametricRegularityUP DiameterWeightLaws
  BallEnlargementBound WeightedEnlargements WeightedCoverComparisonBound TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [half_distance_ball_family]: direct family F
    in Federer 2.9.17, p. 162: balls centered at
    y in B(x,r) minus A, of radius dist(y,A)/2.
    The distance satisfies its abstract infimum laws; no
    selected nearest point or coordinate construction is used. *)
Definition half_distance_ball_family (R : realType) (X : metricType R)
    (A : set X) (d : X -> R) (x : X) (r : R) : set (set X) :=
  [set S | exists y, metric_closed_ball x r y /\ ~ A y /\
    S=metric_closed_ball y (d y/2)%R].

(** Source for [distance_ball_cover_measure_bound]: direct
    weighted-cover estimate in Federer 2.9.17, p. 162:
    psi(B(x,r) minus A) <= c lambda^2 phi(B(x,2r) minus A).
    Apply 2.8.4–2.8.5 with diameter and tau=2, proving
    the selected family countable from positive disjoint masses
    inside the finite-mass reference set. This expands the
    printed countability step without a separability assumption.
    The ball in the right-hand side follows erratum p. 3,
    book p. 162 lines 24–25. *)
Theorem distance_ball_cover_measure_bound (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (A : set X) (d : X -> R)
    (hd : is_metric_set_distance A d) (c delta lambda mu : R) (x : X) (r : R) :
  is_derivation_measure phi -> is_measure psi -> closed A -> (0<=c)%R -> (0<lambda)%R ->
  (0<mu)%R -> has_uniform_fivefold_ball_growth phi setT mu lambda ->
  (forall z, A z -> bounded_centered_ball_ratio_locus psi phi c delta z) ->
  A x -> (0<r)%R -> (r<delta/4)%R -> (r<mu/4)%R ->
  psi (metric_closed_ball x r `\` A)<=
    ((c*lambda^+2)%R)%:E*phi (metric_closed_ball x (2*r)%R `\` A).
Proof.
move=> hphi hpsi hA hc hl hmu hg hbound hx hr hrd hrm.
have hm := derivation_measure_law hphi.
pose F := half_distance_ball_family A d x r.
pose E := metric_closed_ball x (2*r)%R `\` A.
have hgeom y : metric_closed_ball x r y -> ~ A y ->
    (0<d y/2)%R /\ (d y/2<=r/2)%R /\
    metric_closed_ball y (d y/2)%R `<=` E /\
    exists z, A z /\ (mdist y z<3*(d y/2))%R.
  move=> hy hn; exact (@half_distance_ball_geometry R X A d hd x y r hA hx hn hr hy).
have hbounded S : F S -> metric_set_bounded S.
  move=> [y [hy [hn ->]]].
  exact (@covering_closed_ball_bounded R X y (d y/2)%R (ltW (hgeom y hy hn).1)).
have [w hw] := @real_diameter_weight_exists R X F hbounded.
have hFE S : F S -> S `<=` E by move=> [y [hy [hn ->]]]; exact: (hgeom y hy hn).2.2.1.
have hE : phi E< +oo.
  apply: le_lt_trans (@measure_mono R X phi hm E (metric_closed_ball x (2*r)%R)
    (fun _ h => h.1)) _.
  exact (@derivation_measure_bounded_finite R X phi hphi _
    (@covering_closed_ball_bounded R X x (2*r)%R (ltac:(by apply: ltW; rewrite mulr_gt0 // ltr0n)))).
have hnonempty S : F S -> S<>set0.
  move=> [y [hy [hn ->]]] he.
  have hmem : metric_closed_ball y (d y/2)%R y.
    rewrite /metric_closed_ball /= mdistxx; exact: ltW (hgeom y hy hn).1.
  by rewrite he in hmem.
have hwn S (hS : F S) : (0<=w S)%R := @diameter_weight_nonnegative R X F w hw S hS.
have hwb : exists b, forall S, F S -> (w S<=b)%R.
  exists r=> S hS; have [y [hy [hn hSball]]] := hS.
  have hs := (hgeom y hy hn).1; have hsr := (hgeom y hy hn).2.1.
  have hFball : F (metric_closed_ball y (d y/2)%R) by rewrite -hSball.
  rewrite hSball; apply: le_trans (@diameter_weight_ball_bound R X F w hw
    y (d y/2)%R hFball (ltW hs)) _; lra.
have hFm S : F S -> measure_measurable phi S.
  move=> [y [_ [_ ->]]].
  exact (@borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi)
    (metric_closed_ball y (d y/2)%R)
    (@closed_borel_set X _ (@metric_closed_ball_closed R X y (d y/2)%R))).
have hpos S : F S -> 0<phi S.
  move=> [y [hy [hn ->]]].
  exact (@strict_fivefold_growth_ball_positive R X phi lambda mu hm hmu hg y
    (d y/2)%R (hgeom y hy hn).1).
have hcover : metric_closed_ball x r `\` A `<=` \bigcup_(S in F) S.
  move=> y [hy hn]; exists (metric_closed_ball y (d y/2)%R).
  - by exists y.
  - rewrite /metric_closed_ball /= mdistxx; exact: ltW (hgeom y hy hn).1.
have hhat S : F S -> psi (weighted_enlargement F w 2%R S)<=
    ((c*lambda^+2)%R)%:E*phi S.
  move=> hS; have [y [hy [hn hSball]]] := hS.
  have hs := (hgeom y hy hn).1.
  have hFball : F (metric_closed_ball y (d y/2)%R) by rewrite -hSball.
  have hi := @diameter_enlargement_ball_bound R X F w 2%R hw
    (ltac:(by rewrite ler0n)) y (d y/2)%R hFball (ltW hs).
  have he : ((1+2*2)*(d y/2)=5*(d y/2))%R by lra.
  rewrite he in hi; rewrite hSball.
  apply: le_trans (@measure_mono R X psi hpsi _ _ hi) _.
  exact (@distance_ball_fivefold_measure_bound R X phi psi A d hd c delta lambda mu x y r
    hm hpsi hA hc hl hg hbound hx hn hr hy hrd hrm).
exact (@weighted_cover_comparison_bound R X phi psi (metric_closed_ball x r `\` A) E F w
  2%R (c*lambda^+2)%R hm hpsi (ltac:(by rewrite ltr1n))
  (mulr_ge0 hc (sqr_ge0 lambda)) hE hnonempty hwn hwb hFE hFm hpos hcover hhat).
Qed.
