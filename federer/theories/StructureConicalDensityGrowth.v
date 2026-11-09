(** Federer (1969), 3.3.19, pp. 305–306: positive
    conical upper density at every aperture forces the
    original second incidence condition of 3.3.10. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  EuclideanProjectionSpace StructureProjectionKernel StructureCone StructureProjectionCone
  StructurePlaneGrowth StructureConeDensityUP StructureConeCostBounds
  MeasureUP MeasureBasic MeasureRestriction MetricDensities EuclideanBallVolume
  PositiveRadiusLimits PositiveRadiusLimitBounds PositiveRadiusUnboundedValues ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Growth.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Variable mu:set E->\bar R.
Hypothesis hMu:is_measure mu.
Variable A:set E.
Variable p:euclidean_projection_space R 2 1.
Local Notation K:=(structure_projection_kernel (leqnSn 1) p).

(** Source for [structure_radial_supremum_conical_density_upper]:
    a finite bound M on the actual radius-supremum cost
    gives conical upper one-density at most Ms. Closed
    radius-r balls lie in the original strict radius-2r
    cone; this preserves the conventions in 3.3.1 and
    expands the inference of 3.3.19, p. 306. *)
Lemma structure_radial_supremum_conical_density_upper (a:E) (delta s M:R):
  0<delta ->0<s ->
  (structure_plane_radial_supremum 1 mu A a K delta s<=M%:E)%E ->
  (upper_metric_density 1 (measure_restrict mu (A `&` structure_cone K a +oo s)) a<=(M* s)%:E)%E.
Proof.
move=>hDelta hs hBound.
have hHalf:0<delta/2 by lra.
apply:(@positive_radius_upper_eventual_bound R _ (M* s)%:E (delta/2) hHalf)=>r /andP[hr hrSmall].
have hTwice:0<2* r by lra.
have hTwiceSmall:2* r<delta by lra.
have hCost:(structure_cone_cost (leqnSn 1) mu A (a,p) (2* r) s<=M%:E)%E.
  apply:le_trans _ hBound;apply:extended_real_sup_upper.
  exists (2* r);split=>//;by apply/andP;split.
have hMass:=(@structure_cone_cost_mass_bound R 2 1 (leqnSn 1) mu A p a (2* r) s M hTwice hs).1 hCost.
rewrite !expr1 in hMass.
pose T:=(A `&` structure_cone K a +oo s) `&` metric_closed_ball a r.
have hSubset:T `<=` A `&` structure_cone K a (2* r)%:E s.
  move=>x [[hxA hxCone] hxBall];split=>//.
  have [hAngle _]:=(@structure_projection_coneE R 2 1 (leqnSn 1) p a +oo s x).1 hxCone.
  apply:(@structure_projection_coneE R 2 1 (leqnSn 1) p a (2* r)%:E s x).2.
  split=>//;rewrite lte_fin.
  have hNorm:N (x-a)<=r by rewrite -inner_metric_distanceE metric_sym.
  lra.
have hOriginalMass:= le_trans (@measure_mono R E mu hMu T _ hSubset) hMass.
have hInverse:(0<=((2* r)%:E)^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hTwice.
have hScaled:= lee_wpmul2r hInverse hOriginalMass.
have hScalar:(((M*(2* r)* s)%:E/(2* r)%:E)=(M* s)%:E)%E.
  rewrite inver (gt_eqF hTwice) -EFinM;apply:(congr1 (fun x:R=>x%:E)).
  have hrN:r!=0 by rewrite gt_eqF.
  field;by rewrite hrN.
rewrite hScalar in hScaled.
by rewrite /metric_ball_density /measure_restrict euclidean_unit_ball_volume1 expr1.
Qed.

(** Source for [structure_positive_conical_density_infinite_growth]:
    a fixed positive lower conical upper density for every
    0<s<1 forces the original S2 infinite growth at
    every positive radial cutoff. This is precisely the
    order inference from p. 305 to p. 306 in 3.3.19;
    no trichotomy or extra exceptional set is assumed. *)
Theorem structure_positive_conical_density_infinite_growth (a:E) (c:R):
  0<c ->(forall s:R,0<s ->s<1 ->
    (c%:E<=upper_metric_density 1 (measure_restrict mu (A `&` structure_cone K a +oo s)) a)%E) ->
  structure_plane_infinite_growth 1 mu A a K.
Proof.
move=>hc hDensity delta hDelta.
apply:positive_radius_upper_infinite_from_spikes=>b d hd.
pose M:= Num.max b 0+1.
have hBMax:b<=Num.max b 0 by rewrite le_max lexx.
have hMax0:0<=Num.max b 0 by rewrite le_max lexx orbT.
have hM:0<M by rewrite /M;lra.
have hBM:b<M by rewrite /M;lra.
pose s:= Num.min (Num.min d 1) (c/(2* M))/2.
have hScale:0<c/(2* M) by rewrite divr_gt0 //;lra.
have hMin:0<Num.min (Num.min d 1) (c/(2* M)) by rewrite !lt_min hd ltr01 hScale.
have hs:0<s by rewrite /s divr_gt0.
have hsMin:s<Num.min (Num.min d 1) (c/(2* M)) by rewrite /s;lra.
have hFirst:Num.min (Num.min d 1) (c/(2* M))<=Num.min d 1 by rewrite ge_min lexx.
have hsD:s<d.
  have h:Num.min d 1<=d by rewrite ge_min lexx.
  exact:lt_le_trans hsMin (le_trans hFirst h).
have hsOne:s<1.
  have h:Num.min d 1<=1 by rewrite ge_min lexx orbT.
  exact:lt_le_trans hsMin (le_trans hFirst h).
have hLast:Num.min (Num.min d 1) (c/(2* M))<=c/(2* M) by rewrite ge_min lexx orbT.
have hSmall:s<c/(2* M):= lt_le_trans hsMin hLast.
have hMS:M* s<c.
  rewrite ltr_pdivlMr in hSmall;last by lra.
  nra.
exists s;split;first by apply/andP;split.
apply:(le_trans (lee_tofin (ltW hBM))).
rewrite leNgt;apply/negP=>hTooSmall.
have hUpper:= @structure_radial_supremum_conical_density_upper a delta s M hDelta hs (ltW hTooSmall).
have hBoth:= le_trans (hDensity s hs hsOne) hUpper.
rewrite lee_fin in hBoth;lra.
Qed.
End Growth.
