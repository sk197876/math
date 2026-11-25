(** Federer (1969), 3.3.19, pp. 303–304:
    both original alternatives give the local boundary
    weight bound. Every hit mass is the actual finite
    weighted count and the centre-in-S case uses
    the exact retracted centre identity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularTrigonometrySealed CircularDiscTreeUP CircularDiscHitMeasureUP CircularDiscHitMeasureLaws
  CircularDiscHitCount CircularDiscOwnHitMass CircularDiscConvexHitMass FiniteCellHitMeasureUP
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Budget.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation Sin:=(@CircularTrigonometry.sine R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_local_boundary_budget]:
    the complete local inequality lambda psi_(n+1)
    (B intersect S)<= b-|f(xi(B))-c(B)| in
    3.3.19, pp. 303–304. The
    inside-centre case uses the actual radius mass;
    the outside-centre case uses the actual halfplane
    child count. Numeric margins are precisely those
    later discharged by the original diameter cutoff. *)
Theorem circular_disc_local_boundary_budget j (lam:R) (c:E) (S:set E) (y:E):
  0<lam ->lam<((j+4)%:R-1)* Sin (p/(j+4)%:R) ->
  lam*(1/2+((j+4).+1)%:R^-1)<((j+4)%:R-1)* Sin (p/(j+4)%:R)-1 ->
  c \in H j.+1 ->S!=set0 ->is_inner_convex S ->
  metric_closed_ball c (rho j.+1) y ->(S c ->y= c) ->
  (lam%:E* psi j.+2 (metric_closed_ball c (rho j.+1) `&` S)<=
    ((((j+4)%:R-1)* Sin (p/(j+4)%:R))* rho j.+1-mdist y c)%:E)%E.
Proof.
move=>hLam hFirst hSecond hc hNonempty hConvex hBall hCentre.
pose T:= metric_closed_ball c (rho j.+1) `&` S.
pose v:R:=#|` @circular_disc_hit_indices R H j.+2 T|%:R* rho j.+2.
have hValue:psi j.+2 T= v%:E.
  rewrite (hPsi j.+2);exact:erefl.
change (is_true ((lam%:E* psi j.+2 T<=
    ((((j+4)%:R-1)* Sin (p/(j+4)%:R))* rho j.+1-mdist y c)%:E)%E)).
rewrite hValue -EFinM lee_fin.
have hRadius:0<rho j.+1:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R)
  rho (@FactorialDiscScales.laws R) j.+1.
have hDistance:mdist y c<= rho j.+1 by rewrite metric_sym;exact hBall.
case:(pselect (S c))=>hInside.
- have hStep:= @circular_disc_hit_refinement_decreases R H psi hPsi hH j.+1 T.
  have hSubset:T `<=` metric_closed_ball c (rho j.+1) by move=>x [hx _].
  have hEarlier:= @measure_mono R E (psi j.+1)
    (@circular_disc_hit_is_measure R H psi hPsi j.+1) T _ hSubset.
  rewrite (@circular_disc_own_hit_mass R H hH psi hPsi j.+1 c hc) in hEarlier.
  have hBound:= le_trans hStep hEarlier.
  rewrite hValue lee_fin in hBound.
  rewrite (hCentre hInside) mdistxx subr0.
  have hWeighted:= ler_wpM2l (ltW hLam) hBound.
  have hMargin:= ler_wpM2r (ltW hRadius) (ltW hFirst).
  exact:(le_trans hWeighted hMargin).
- have hOutside:= @circular_disc_convex_outside_hit_mass R H hH psi hPsi j.+1 c S
    hc hNonempty hConvex hInside.
  have hIndex:(j.+1+4=(j+4).+1)%N by rewrite addSn.
  rewrite -/T hValue hIndex lee_fin in hOutside.
  have hWeighted:= ler_wpM2l (ltW hLam) hOutside.
  have hMargin:= ler_wpM2r (ltW hRadius) (ltW hSecond).
  rewrite [leRHS]mulrA !div1r in hWeighted.
  rewrite mulrBl !mul1r in hMargin.
  have hLast:(((j+4)%:R-1)* Sin (p/(j+4)%:R))*rho j.+1-rho j.+1<=
      (((j+4)%:R-1)* Sin (p/(j+4)%:R))*rho j.+1-mdist y c.
    by rewrite lerD2l lerN2.
  exact:(le_trans hWeighted (le_trans hMargin hLast)).
Qed.
End Budget.
