(** Federer (1969), 3.2.33, p. 270: construct
    the actual smooth strictly increasing primitive from the
    independently specified interval series. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealNormUP NormHigherCurveDerivativeUP NormDifferentialUP NormDifferentialLocal NormClassOneUP NormRegularity
  NormRegularityOperations RealMetricBackground RealOpenIntervals LipschitzUP
  DenseSmallIntervalFamilyUP IntervalBumpSeriesUP IntervalBumpPrimitiveUP ScalarClassZeroMeasurable
  BoundedScalarPrefixPrimitive ContinuousScalarPrefixDifferentiation BoundedScalarPrefixIncrements
  DensePositivePrimitiveStrict RealCurvePolynomialDerivatives ScalarSmoothPrimitive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_bump_primitive_exists]: all assertions
    about g in the smooth example of Federer 3.2.33,
    p. 270. Bounded measurability proves actual primitive
    existence, continuity proves differentiation at every point
    of T, and the higher recursion proves smoothness. Integral
    increments prove a unit Lipschitz bound. Dense positivity
    proves strict increase and the exact zero-derivative locus.
    No primitive, injectivity or regularity is assumed to exist. *)
Theorem interval_bump_primitive_exists (R:realType) (a b:nat->R) (phi psi:R->R):
  is_dense_small_interval_family a b ->is_interval_bump_series a b phi psi ->
  exists g:R->R,is_interval_bump_primitive a b psi g.
Proof.
move=>hFamily hSeries.
pose T:=real_open_interval (0:R) 1.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
have hZero:norm_class_zero N N (fun _=>True) psi:=(interval_bump_series_smooth hSeries 0%N).1.
have hMeas:=scalar_class_zero_extended_measurable hZero.
have [g hPrimitive]:=bounded_scalar_prefix_primitive_exists hMeas (interval_bump_series_bounds hSeries).
have hInterior t (ht:T t):norm_domain_interior N T t.
  have [ht0 ht1]:=ht.
  pose r:R:=Order.min t (1-t).
  have hr:0<r by rewrite /r lt_min ht0 subr_gt0 ht1.
  exists r; split; first exact hr.
  move=>v hv.
  have hNorm: -r<v<r by move:hv; rewrite /N ltr_norml.
  have /andP [hv0 hv1]:=hNorm.
  have hrt:r<=t by rewrite /r ge_min lexx.
  have hr1:r<= 1-t by rewrite /r ge_min lexx orbT.
  split; lra.
have hActual t (ht:T t):=continuous_scalar_prefix_derivative hZero hPrimitive ht.
have hDifferential t (ht:T t):has_norm_differential N N T g t
    (@scalar_coefficient_linear_map R R^o (psi t)).
  have hFull:=real_curve_derivative_full_differential (hActual t ht).
  exact:(@norm_differential_restrict R R^o R^o N N (fun _=>True) T g t
    (@scalar_coefficient_linear_map R R^o (psi t)) (fun t (_:T t)=>Logic.I) (hInterior t ht) hFull).
have hPsiSmooth:norm_class_all_orders hN hN T psi.
  move=>k; exact:(@norm_class_open_restriction R R^o R^o N N hN hN
    (fun _=>True) T psi k (fun t (_:T t)=>Logic.I) hInterior (interval_bump_series_smooth hSeries k)).
have hSmooth:=scalar_primitive_of_smooth_density_smooth hPsiSmooth hDifferential.
have hIncrement:=bounded_scalar_prefix_increment (interval_bump_series_bounds hSeries) hPrimitive.
have hStrict:=dense_positive_primitive_strictly_increasing hFamily
  (interval_bump_series_positive hSeries) hActual (fun u v hu huv hv=>(andP (hIncrement u v hu huv hv)).1).
exists g; constructor.
- exact hPrimitive.
- exact hDifferential.
- exact hSmooth.
- exact hStrict.
- split; first exact:ler01.
  move=>u v [hu0 hu1] [hv0 hv1].
  rewrite !real_line_metric_distanceE mul1r.
  have [huv|hvu]:=leP u v.
  + have /andP [h0 h1]:=hIncrement u v (ltW hu0) huv (ltW hv1).
    have hNormG:`|g u-g v|= g v-g u by rewrite distrC (ger0_norm h0).
    have hNormUV:`|u-v|= v-u by rewrite distrC ger0_norm // subr_ge0.
    by rewrite hNormG hNormUV.
  + have /andP [h0 h1]:=hIncrement v u (ltW hv0) (ltW hvu) (ltW hu1).
    have hNormUV:`|u-v|= u-v by rewrite ger0_norm // subr_ge0; exact:ltW hvu.
    by rewrite (ger0_norm h0) hNormUV.
- move=>t ht; split.
  + move=>hZeroT hV; have hPositive:0<psi t:=(interval_bump_series_positive hSeries t).2 hV.
    by rewrite hZeroT ltxx in hPositive.
  + move=>hNot; apply/eqP; rewrite eq_le (andP (interval_bump_series_bounds hSeries t)).1 andbT leNgt.
    apply/negP=>hp; exact:hNot ((interval_bump_series_positive hSeries t).1 hp).
Qed.
