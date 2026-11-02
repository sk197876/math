(** Federer (1969), 3.2.26(1), p. 261: spherical
    and Hausdorff measure agree on every finite (H^m,m)-
    rectifiable set. No source measurability is added. Follow
    the printed upper-density argument through a true measure hull. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RectifiableSetUP
  RectifiableBorelMeasureHull RectifiableDensityTangent MeasureHullMetricDensities MeasureHull
  HausdorffMeasure HausdorffSphericalComparison HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureSplit MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel MetricDensities PartialFunctionUP
  SphericalMetricDensityTheorems ExtendedPowerGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_spherical_hausdorff_agreement]: the
    first comparison in the proof of 3.2.26, p. 261,
    combined with H^m<=S^m from 2.10.2, p. 171.
    Apply 2.10.19(3) below the density-one threshold and
    let the threshold approach one. A genuine measure hull
    justifies 3.2.19 without a W-measurability premise. All
    natural dimensions and zero or infinite intermediate masses
    are retained. *)
Theorem rectifiable_spherical_hausdorff_agreement (R:realType) m n (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose S:=@spherical_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hS:=@spherical_measure_is_measure R X m.
have hRegular:=@hausdorff_measure_borel_regular R X m.
pose mu:=measure_restrict H W.
have hMu:=measure_restrict_is_measure hH W.
have [M [hMBorel [hHull hMRect]]]:=rectifiable_borel_measure_hull hRect.
have hWM:=measure_hull_subset hHull.
have hMMeas:=borel_regular_borel_measurable hH hRegular hMBorel.
have hDensity:=(federer_3_2_19 hMRect hMMeas).1.
pose B:set X:=[set w|upper_metric_density m mu w= 1].
have hNullH:H (W `\` B)=0.
  apply:(measure_null_subset hH _ hDensity)=>w [hw hn]; split; first exact:hWM w hw.
  move=>[hGraph hPlane]; apply:hn.
  have hHullDensity:=@measure_hull_upper_metric_density R X H m W M w hH hRegular hHull.
  change (upper_metric_density m (measure_restrict H W) w= 1).
  rewrite hHullDensity; exact:((@metric_density_graph R X m (measure_restrict H M) w 1).1 hGraph).1.
have hNullS:S (W `\` B)=0.
  have hBound:=@spherical_measure_le_double_hausdorff_measure R X m (W `\` B).
  change (is_true (S (W `\` B)<=((2:R)^+m)%R%:E*H (W `\` B))) in hBound.
  rewrite hNullH mule0 in hBound.
  apply/eqP; by rewrite eq_le hBound (measure_nonnegative hS (W `\` B)).
have hSubset:W `<=` B `|` (W `\` B).
  move=>w hw; have [hb|hb]:=pselect (B w); first by left.
  right; by split.
have hSW:S W<=S B.
  have hBound:=@measure_binary_cover R [the choiceType of X] S hS W B (W `\` B) hSubset.
  change (is_true (S W<=S B+S (W `\` B))) in hBound.
  by rewrite hNullS adde0 in hBound.
have hClosed (C:set X):closed C ->measure_measurable mu C.
  move=>hC; apply:measure_restrict_measurable.
  exact:(borel_regular_borel_measurable hH hRegular (closed_borel_set hC)).
have hUpper:S W<=H W.
  apply:(@extended_power_geometric_squeeze R (H W) (S W) 1%N (measure_nonnegative hH W)).
  move=>lambda hLambda.
  have hLambdaPositive:(0<lambda)%R:=lt_trans ltr01 hLambda.
  pose t:R:=(lambda^-1)%R.
  have ht:(0<t)%R by rewrite /t invr_gt0.
  have ht1:(t<1)%R by rewrite /t invf_lt1.
  have hDensityBound w:B w ->t%:E<upper_metric_density m mu w.
    move=>hw; rewrite hw lte_fin; exact ht1.
  have hBound:=@federer_2_10_19_3 R X m mu B setT t hMu hClosed openT
    (subsetT B) hDensityBound.
  change (is_true (t%:E*S B<=mu setT)) in hBound.
  rewrite /mu /measure_restrict setIT in hBound.
  have hScaled:=lee_wpmul2l (lee_tofin (ltW hLambdaPositive)) hBound.
  rewrite muleA -EFinM /t mulfV ?gt_eqF // mul1e in hScaled.
  rewrite expr1; exact:le_trans hSW hScaled.
apply/eqP; rewrite eq_le hUpper /=.
exact:(@hausdorff_measure_le_spherical_measure R X m W).
Qed.
