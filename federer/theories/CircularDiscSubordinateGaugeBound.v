(** Federer (1969), 3.3.19, pp. 303–304:
    combine the single-finest-disc and first-split
    alternatives for every original small cover member
    which contains an original finest-level disc. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex MetricClosedBalls MetricDiameter CoveringFamilyUP
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometrySealed
  CircularDiscTreeUP CircularDiscHitCount CircularDiscHitMeasureUP CircularDiscHitMeasureLaws CircularDiscOwnHitMass
  CircularDiscFirstSplitUP CircularDiscFirstSplit CircularDiscFirstSplitCutoff CircularDiscFirstSplitGaugeBound
  PlanarDiscFirstGauge FiniteCellHitMeasureUP IntegralGeometricGauge MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Bound.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation q:=(@integral_geometric_gauge R 2 1 (leqnSn 1) 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_subordinate_gauge_bound]:
    both alternatives imply zeta_1(S)>=lambda
    psi_(nu+1)(S), exactly the estimate in
    3.3.19, pp. 303–304. The
    positive diameter cutoff is proved from the
    original lambda, and the first split and
    all its scalar margins are discharged. *)
Theorem circular_disc_subordinate_gauge_bound (lam:R):0<lam ->lam<p ->
  exists d:R,0<d /\forall nu (S:set E),
    open S ->is_inner_convex S ->(extended_metric_diameter S<=d%:E)%E ->
    (exists z,z \in H nu /\metric_closed_ball z (rho nu) `<=` S) ->
    (lam%:E* psi nu.+1 S<=q S)%E.
Proof.
move=>hLam hLamP.
have [d [hd hCutoff]]:=@circular_disc_first_split_cutoff R H hH lam hLam hLamP.
exists d;split=>//;move=>nu S hOpen hConvex hDiameter [z [hz hInside]].
have hBound:metric_set_bounded S:=le_lt_trans hDiameter (ltry d).
case:(leqP 2 #|` @circular_disc_hit_indices R H nu S|)=>[hMany|hFew].
- have [j [hj hFirst]]:=@circular_disc_first_split_exists R H S nu hMany.
  have hPositive:=@circular_disc_first_split_positive R H S hH j hFirst.
  case:j hj hFirst hPositive=>[|j] hj hFirst hPositive;first by [].
  have [hN [hCoefficient hMargin]]:=hCutoff j S hFirst hDiameter.
  have hOriginal:=@circular_disc_first_split_gauge_bound R H hH psi hPsi j lam S
    hLam hCoefficient hMargin hOpen hConvex hBound hFirst.
  have hLater:=@circular_disc_hit_later_decreases R H hH psi hPsi j.+2 nu.+1 S hj.
  have hScaled:=lee_wpmul2l (lee_tofin (ltW hLam)) hLater.
  exact:(le_trans hScaled hOriginal).
- have hOne:(#|` @circular_disc_hit_indices R H nu S|<=1)%N by move:hFew;rewrite ltnS.
  have hCast:(#|` @circular_disc_hit_indices R H nu S|%:R<=(1%N)%:R:>R) by rewrite ler_nat.
  have hRadius:0<rho nu:=@factorial_disc_radius_positive R (@FactorialDiscScales.count R)
    rho (@FactorialDiscScales.laws R) nu.
  have hEarlier:(psi nu S<=(rho nu)%:E)%E.
    rewrite (hPsi nu) lee_fin.
    have hProduct:=ler_wpM2r (ltW hRadius) hCast.
    by rewrite mul1r in hProduct.
  have hStep:=@circular_disc_hit_refinement_decreases R H psi hPsi hH nu S.
  have hMass:=le_trans hStep hEarlier.
  have hWeighted:=lee_wpmul2l (lee_tofin (ltW hLam)) hMass.
  have hCoefficient:(lam* rho nu<=p* rho nu)%R:=ler_wpM2r (ltW hRadius) (ltW hLamP).
  have hDisc:=@planar_contained_disc_first_gauge_lower R z (rho nu) S hRadius hOpen hInside.
  apply:(le_trans hWeighted);rewrite -EFinM.
  exact:(le_trans (lee_tofin hCoefficient) hDisc).
Qed.
End Bound.
