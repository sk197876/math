(** Federer (1969), 3.3.19, p. 306: uniformly
    every original parent-piece ball has mass at most
    its radius plus an arbitrarily small parent-scale error. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerUnitNormalization MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometrySealed
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscParentAnnulus CircularDiscPieceHausdorffMass
  CircularDiscCaps CircularDiscUniformCapMass CircularCapChordBudget CircularBallCapGeometry
  NaturalScaledReciprocalTail HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Approximation.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Local Notation pi:=(@CircularTrigonometry.half_period R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_approximate_parent_ball_mass]:
    for each positive b, all sufficiently late original
    parents satisfy H1(A intersect parent intersect B(a,t))
    <=t+b rho_j, for every original vertex a in that
    parent and every t>=0. Uniform actual cap mass,
    original annuli and the exact circular chord budget
    prove this supporting estimate for the final assertion
    of 3.3.19, p. 306. The residual parent-scale error
    is not used alone at radii comparable to child radii. *)
Theorem circular_disc_approximate_parent_ball_mass (b:R):0<b ->exists J:nat,
  forall j (z a:E) (t:R),(J<=j)%N ->z \in H j ->A a ->
  metric_closed_ball z (rho j) a ->0<=t ->
  (mu ((A `&` metric_closed_ball z (rho j)) `&` metric_closed_ball a t)<=(t+b* rho j)%:E)%E.
Proof.
move=>hb.
pose e:= b/4.
pose eps:= b/8.
have he:0<e by rewrite /e;lra.
have hEps:0<eps by rewrite /eps;lra.
have hESquare:0<e^+2 by rewrite exprn_gt0.
have h24:0<(24:R) by rewrite ltr0n.
have [J1 hUniform]:= @circular_disc_uniform_cap_mass R H hH A hA eps hEps.
have [J2 hSmall]:= @natural_scaled_reciprocal_tail R 24 (e^+2) h24 hESquare.
exists (maxn J1 J2)=>j z a t hj hz ha haBall ht.
have hj1:(J1<=j)%N:= leq_trans (leq_maxl J1 J2) hj.
have hj2:(J2<=j+4)%N:= leq_trans (leq_trans (leq_maxr J1 J2) hj) (leq_addr 4 j).
have [_ hNsmall]:= hSmall _ hj2.
pose r:= rho j.
have hr:0<r:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hrN:r!=0 by rewrite gt_eqF.
have hMu:= @hausdorff_measure_is_measure R E 1.
pose T:=(A `&` metric_closed_ball z r) `&` metric_closed_ball a t.
have hFull:(mu T<=(2* r)%:E)%E.
  rewrite -(@circular_disc_piece_Hausdorff_mass R H hH A hA j z hz).
  apply:(@measure_mono R E mu hMu)=>x [hx _];exact:hx.
pose U:= t/r+e.
have hU:0<=U.
  have hQuotient:0<=t/r by apply:divr_ge0=>//;exact:ltW hr.
  rewrite /U;lra.
have hScalar:r* U= t+r* e by rewrite /U;field.
case:(leP U 2)=>[hU2|hLarge].
- have [g [hg [hgp [hCos hBudget]]]]:= @circular_ball_cap_angle_budget R U hU hU2.
  have [hDeficit hUpper]:= @circular_disc_original_parent_annulus R H hH A hA j z a hz ha haBall.
  pose d:= N (a-z).
  have hn:(4<=j+4)%N by exact:leq_addl.
  have hNPositive:0<((j+4)%:R:R) by rewrite ltr0n addn_gt0 orbT.
  have hNFour:(4<=(j+4)%:R:>R) by rewrite ler_nat.
  have hQuarter:((j+4)%:R:R)^-1<=1/4.
    rewrite -[X in X<=_]div1r ler_pdivrMr //;lra.
  have hdHalf:r/2<=d.
    have hProduct:= ler_wpM2l (ltW hr) hQuarter.
    change (is_true (r-2* r/(j+4)%:R<=d)) in hDeficit;nra.
  have hd:0<d by lra.
  have hdN:d!=0 by rewrite gt_eqF.
  pose eta:= inner_unit_normalization (@euclidean_inner_productP R 2) (a-z).
  have hEta:N eta= 1:= inner_unit_normalization_norm hd.
  have hVertex:a= z+d*:eta.
    rewrite /eta /inner_unit_normalization -/d scalerA mulfV // scale1r.
    by rewrite addrC subrK.
  have ht2:t<=2* r.
    have hSmallRatio:t/r<=2 by rewrite /U in hU2;lra.
    move:hSmallRatio;rewrite ler_pdivrMr //;lra.
  have hSubset:T `<=` A `&` circular_disc_cap z r eta g.
    move=>x [[hxA hxParent] hxBall];split=>//.
    have [hXDeficit _]:= @circular_disc_original_parent_annulus R H hH A hA j z x hz hxA hxParent.
    exact:(@circular_ball_cap_containment R z a x eta r d t e g (j+4)%N hr hn hEta hVertex
      hDeficit hUpper hXDeficit hxParent ht ht2 hxBall he hNsmall hCos).
  have hTestBound:= @measure_mono R E mu hMu T _ hSubset.
  have [_ hCapUpper]:= hUniform j z eta g hj1 hz hEta hg hgp.
  have hDen:0<2* r by lra.
  have hCapMass:(mu (A `&` circular_disc_cap z r eta g)<=((g/pi+eps)*(2* r))%:E)%E.
    move:(ltW hCapUpper);by rewrite inver (gt_eqF hDen) (lee_pdivrMr _ _ hDen) -EFinM.
  have hBoth:= le_trans hTestBound hCapMass.
  have hBudgetScaled:= ler_wpM2l (ltW hr) hBudget.
  have hFinal:(g/pi+eps)*(2* r)<=t+b* r.
    rewrite /e /eps in hScalar;rewrite /eps;nra.
  exact:(le_trans hBoth (lee_tofin hFinal)).
- have hLargeScaled:r*2<r*U by rewrite ltr_pM2l.
  have hFinal:2* r<=t+b* r by rewrite /e in hScalar;nra.
  exact:(le_trans hFull (lee_tofin hFinal)).
Qed.
End Approximation.
