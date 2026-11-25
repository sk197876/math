(** Federer (1969), 3.3.19, p. 302: the original
    compact nested-disc set has Hausdorff length at most two.
    Use actual arbitrarily fine level covers, the recursive
    finite count bound and conserved total radii. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  MetricDiameterUP MetricDiameter CaratheodoryLimitUP CaratheodoryBorelRegular
  MetricScaleEnvelopeUP HausdorffMeasure HausdorffMeasureUP HausdorffDiameterCost
  HausdorffCutoffFiniteCover FactorialDiscScalesUP FactorialDiscScalesSealed
  FactorialDiscScaleLaws CircularDiscTreeUP CircularDiscLimitUP CircularDiscTreeCountUpper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Upper.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).

(** Source for [circular_disc_limit_Hausdorff_upper]: literal
    H^1(A)<= 2 from the sum of original level diameters in
    3.3.19, p. 302. Actual covers work at every positive
    real cutoff; no measure or diameter bound is assumed. *)
Theorem circular_disc_limit_Hausdorff_upper (H:nat->{fset E}) (A:set E):
  is_circular_disc_tree H ->is_circular_disc_limit H A ->
  @hausdorff_measure R E 1 A<=(2:R)%:E.
Proof.
move=>hH hA.
apply:(caratheodory_limit_least (@hausdorff_measure_specification R E 1))=>delta nu hd hn.
have [i hCut]:=reciprocal_metric_cutoffs_cofinal hd.
pose a:R:=(i.+1%:R^-1)%R.
have ha:(0<a)%R by rewrite /a invr_gt0 ltr0n.
have h3:(0<(3:R))%R by rewrite ltr0n.
have hThird:(0<a/3)%R by rewrite divr_gt0.
have [J hJ]:=@factorial_disc_radius_small R N rho hs (a/3)%R hThird.
pose I:=[the finType of ((H J):Type)].
pose K (i:I):set E:=metric_closed_ball (val i) (rho J).
have hR:(0<=rho J+rho J)%R.
  have hh:=factorial_disc_radius_positive hs J;lra.
have hDiameter q:extended_metric_diameter (K q)<=(rho J+rho J)%R%:E.
  apply:(metric_diameter_least (extended_metric_diameter_specification (K q))).
  - by rewrite lee_fin.
  - move=>x y hx hy;rewrite lee_fin;exact:metric_closed_ball_diameter_bound hx hy.
have hSmall:(rho J+rho J<a)%R by have hh:=hJ J (leqnn J);lra.
have hCap:(rho J+rho J)%R%:E<=delta.
  apply:le_trans _ hCut;rewrite lee_fin;exact:ltW hSmall.
have hCover:A `<=` \bigcup_(i:I) K i.
  move=>x hx;have [z [hz hxz]]:=(hA x).1 hx J.
  exists ([` hz]%fset);first exact Logic.I.
  exact hxz.
have hBound:=@hausdorff_cutoff_finite_equal_diameter_cover R E I 1 delta nu A K
  (rho J+rho J)%R hn hR hCap hDiameter hCover.
rewrite hausdorff_normalisation_one expr1 mul1r in hBound.
have hCount:(#|I|<=N J)%N.
  have hh:=@circular_disc_tree_count_upper R H hH J.
  by rewrite /I -cardfE.
have hCountR:((#|I|)%:R<=(N J)%:R:>R)%R by rewrite ler_nat.
have hCost:((#|I|)%:R*(rho J+rho J)<= 2)%R.
  have hScaled:=ler_wpM2r hR hCountR.
  have hBudget:=@factorial_disc_count_radius R N rho hs J.
  have hExact:((N J)%:R*(rho J+rho J)= 2)%R by nra.
  by rewrite hExact in hScaled.
apply:le_trans hBound _;by rewrite lee_fin.
Qed.
End Upper.
