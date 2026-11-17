(** Federer (1969), 3.4.9, p. 337:
    every sufficiently small positive radius gives the
    original corrected stratification with a common ball
    neighbourhood. The strata themselves are retained and
    restricted; the radius has no exceptional-value condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP AnalyticVarietyGermUP
  FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP
  AnalyticFiniteStratificationExistence Federer348Stratification
  AnalyticStratificationBallRestriction FiniteNormCommonClosedBall MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_9_uniform_balls]: the entire second
    assertion of 3.4.9, p. 337, with all
    corrected conclusions of 3.4.8(11). The original
    hypotheses alone choose the strata and common radius. *)
Theorem federer_3_4_9_uniform_balls (R:realType) n
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    m (U0 S0:set (R_n R n)):
  @is_analytic_variety_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 set0 ->
  @AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha) = m ->
  U0 0 ->@is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U0 S0 ->
  @set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S0 = beta ->
  exists mu,exists V S G:'I_mu->set (R_n R n),exists rho:R,
    0<rho /\@is_analytic_finite_stratification R n alpha beta m U0 S0 mu V S G /\
    forall r:R,0<r ->r<rho ->
      @is_analytic_finite_stratification R n alpha beta m U0 S0 mu
        (fun _=>[set x|inner_norm (@euclidean_inner_productP R n) x<r])
        (fun i=>[set x|inner_norm (@euclidean_inner_productP R n) x<r] `&` S i)
        (fun i=>[set x|inner_norm (@euclidean_inner_productP R n) x<r] `&` G i).
Proof.
move=>hAlpha hNonempty hDepth hU00 hS0 hBeta.
have [mu [V [S [G hLaws]]]]:=@federer_3_4_8_11 R n alpha beta m U0 S0
  hAlpha hNonempty hDepth hU00 hS0 hBeta.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hEach i:@open (real_norm_metric_space hNX) (V i) /\V i 0.
  have [hOpen [hZero hInside]]:=analytic_stratification_neighbourhoods hLaws i;by split.
have [rho [hRho hCommon]]:=@finite_norm_common_closed_ball R X NX hNX
  (Finite.clone 'I_mu _) U0 V hS0.1 hU00 hEach.
exists mu,V,S,G,rho;split;first exact:hRho.
split;first exact:hLaws.
move=>r hR hUpper.
have hBall:@open T [set x|NX x<r].
  have hSame:[set x:real_norm_metric_space hNX|NX x<r]=
      [set x:real_norm_metric_space hNX|@mdist R [the metricType R of real_norm_metric_space hNX] (0:X) x<r].
    apply:funext=>x.
    change (is_true (NX x<r)=is_true (NX (0-x)<r)).
    by rewrite /NX sub0r inner_normN.
  rewrite hSame;exact:metric_open_ball_open.
have hClosed i:[set x|NX x<=r] `<=` V i.
  move=>x hx;exact:(hCommon r hR hUpper x hx).2 i.
have hInside:[set x|NX x<r] `<=` U0.
  move=>x hx;exact:(hCommon r hR hUpper x (ltW hx)).1.
exact:(@analytic_stratification_ball_restriction R n alpha beta m U0 S0 mu V S G r
  hLaws hR hBall hInside hClosed).
Qed.
