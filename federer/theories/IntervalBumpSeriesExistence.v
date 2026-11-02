(** Federer (1969), 3.2.33, p. 270: prove existence
    and global smoothness of the printed interval bump series.
    Every differentiated series is normally convergent. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormMetric InnerConvex ScalarNormMetricCompleteness
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormRegularity NormClassOneUP NormClassHigherUP
  PositiveUnitIntervalBumpUP DenseSmallIntervalFamilyUP PositiveIntervalBumpDifferentialBounds
  RescaledIntervalBumpDifferentials RescaledIntervalBumpValues ShrinkingIntervalSeriesWeights
  NormGeometricSeriesUniform NormSmoothSeries IntervalBumpSeriesUP IntervalBumpSeriesValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_bump_series_exists]: the displayed
    definition and class-infinity assertion for psi in Federer
    3.2.33, p. 270. Compact support bounds every actual
    derivative of phi. Affine rescaling gives d_j^(j+1-i),
    and geometric tail bounds with finite-prefix absorption
    prove normal convergence at every order. The earlier
    smooth-series theorem identifies all actual derivatives.
    Scalar partial-sum bounds prove the exact positive set;
    no regularity or positivity is assumed for the sum. *)
Theorem interval_bump_series_exists (R:realType) (a b:nat->R) (phi:R->R):
  is_positive_unit_interval_bump phi ->is_dense_small_interval_family a b ->
  exists psi:R->R,is_interval_bump_series a b phi psi.
Proof.
move=>hPhi hFamily.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
have hZ i:is_continuous_multilinear_space N N (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose d j:R:=b j-a j.
pose q:R:= 1/2.
pose Q j t:R:=d j^+j.+1*phi ((t-a j)/d j).
pose P M t:R:=\sum_(j<M) Q j t.
have hq:0<q<1 by rewrite /q; apply/andP; split; lra.
have hD j:0<d j<=q.
  apply/andP; split; first by rewrite /d subr_gt0; exact:(dense_small_interval_endpoints hFamily j).2.1.
  exact:(dense_small_interval_length hFamily j).
have [D [C hDC]]:=positive_interval_bump_differential_bounds hPhi.
have hPhiZero:norm_class_zero N N (fun _=>True) phi:=(positive_interval_bump_smooth hPhi 0%N).1.
have hRescaled j i:exists E:R->Z i,
    norm_class_zero N N (fun _=>True) (Q j) /\
    (forall t,has_norm_higher_differential N ev ZN (fun _=>True) (Q j) i t (E t)) /\
    norm_class_zero N (ZN i) (fun _=>True) E /\
    forall t,ZN i (E t)<=C i*(d j)^+j.+1*((d j)^-1)^+i.
  exact:(@rescaled_interval_bump_differentials R Z ev ZN hZ phi j i (a j) (d j) (C i) (D i)
    (andP (hD j)).1 (ltW (hDC i).2.2.1) hPhiZero (hDC i).1 (hDC i).2.1 (hDC i).2.2.2.1).
pose E j i:=projT1 (cid (hRescaled j i)).
have hE j i:=projT2 (cid (hRescaled j i)).
have hWeights i:exists M:R,0<M /\forall j,C i*(d j)^+j.+1*((d j)^-1)^+i<=q^+j*M.
  exact:(@shrinking_interval_derivative_weights_geometric R d q (C i) i hq (ltW (hDC i).2.2.1) hD).
have [M hM]:=choice hWeights.
have hENorm i j t:ZN i (E j i t)<=q^+j*M i.
  exact:(le_trans ((hE j i).2.2.2 t) ((hM i).2 j)).
have hQBound j t:N (Q j t)<=q^+j*q.
  have hValues:=@rescaled_interval_bump_values R phi j (a j) (b j) t hPhi
    (dense_small_interval_endpoints hFamily j).2.1.
  have hNonnegative:0<=Q j t:=(andP hValues.1).1.
  rewrite /N (ger0_norm hNonnegative) -exprSr.
  apply:le_trans (andP hValues.1).2 _.
  exact:(lerXn2r j.+1 (ltW (andP (hD j)).1) (ltW (andP hq).1) (andP (hD j)).2).
have hIncrement j t (_:True):N (P j.+1 t-P j t)<=q^+j*q.
  rewrite /P big_ord_recr /= addrAC subrr add0r; exact:hQBound.
have [psi [hPointwise [hError hUniform]]]:=@norm_geometric_series_uniform_limit R R^o R^o N hN
  (@scalar_norm_metric_complete R) (fun _=>True) P q q hq (ltW (andP hq).1) hIncrement.
have hLimit e (he:0<e):exists K:nat,forall L,(K<=L)%N ->forall t,`|P L t-psi t|<e.
  have [K hK]:=hUniform e he; exists K=>L hL t; exact:(hK L hL t Logic.I).
have hConvex:is_inner_convex (@setT R^o) by move=>x y _ _ t h0 h1.
have hopen t (_:True):norm_domain_interior N (fun _=>True) t.
  exists 1; split; first exact:ltr01; by move=>v hv.
have hNormal e (he:0<e):exists K:nat,forall L,(K<=L)%N ->forall t,True ->N ((\sum_(j<L) Q j t)-psi t)<e.
  have [K hK]:=hLimit e he; exists K=>L hL t _; exact:(hK L hL t).
have [G [hSmooth _]]:=@norm_geometrically_dominated_smooth_series R R^o R^o N N hN hN
  (@scalar_norm_metric_complete R) Z ev ZN hZ (fun _=>True) Q E psi q M
  hConvex hopen hq (fun i=>ltW (hM i).1) (fun j=>(hE j 0%N).1)
  (fun j i t=>(hE j i).2.1 t) (fun j i=>(hE j i).2.2.1)
  (fun i j t _=>hENorm i j t) hNormal.
have [hBounds hPositive]:=interval_bump_series_values hPhi hFamily hLimit.
exists psi; constructor.
- exact hLimit.
- exact hBounds.
- exact hPositive.
- exact hSmooth.
Qed.
