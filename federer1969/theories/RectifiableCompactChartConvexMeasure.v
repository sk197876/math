(** Federer (1969), 3.2.26(2), p. 261: the
    convex integral-geometric measure of each compact chart
    is at most its Hausdorff measure. Every density,
    cover, null remainder and limiting estimate is proved
    using the independent measure specifications. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableCompactChartsUP RectifiableCompactChartLaws CompactChartGeometricDensities
  RectifiableChartConvexCovers RectifiableSetUP EuclideanFiniteMeasureVitali
  MetricDensityConvexCoverBound IntegralGeometricGauge IntegralGeometricMeasure ProjectionMeasureUP
  GeometricHausdorffNullComparison InnerConvex HausdorffMeasure HausdorffClosedCoverAgreement
  MetricDensities MeasureUP MeasureBasic MeasureRestriction MeasureRestrictionSupport
  MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP BorelRegularRestriction TopologicalBorel
  BorelClosedProjection CaratheodoryLimitUP CaratheodoryBorelRegular MetricScaleEnvelopeUP
  MetricScaleCutoffCost ExtendedPowerGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_chart_convex_integral_geometric_upper]:
    conclusion of the compact-piece calculation in 3.2.26(2),
    p. 261. At each cutoff the fine ball relation
    gives the factor (1+delta)^2. The independently proved
    rough Hausdorff-null comparison pays for the omitted set;
    letting delta decrease to zero gives coefficient one. *)
Theorem compact_chart_convex_integral_geometric_upper (R:realType) m n
    (hmn:(m<=n)%N) (lambda:R) (K:set (R_n R m)) (psi:R_n R m->R_n R n) (t: \bar R):
  (0<lambda)%R ->is_uniform_compact_rectifiable_chart lambda K psi ->1<=t ->
  @convex_integral_geometric_measure R n m hmn t (psi @` K)<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (psi @` K).
Proof.
move=>hLambda hChart ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose W:=psi @` K.
pose H:=@hausdorff_measure R X m.
pose Q:=@convex_integral_geometric_measure R n m hmn t.
pose mu:=measure_restrict H W.
have hH:=@hausdorff_measure_is_measure R X m.
have hHBorel:=@hausdorff_measure_borel_regular R X m.
have hWBorel:@borel_set X W.
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R X)
    (uniform_compact_chart_image_compact hChart))).
have hRect:=uniform_compact_chart_finite_rectifiable hChart.
have hMu:=measure_restrict_is_measure hH W.
have hMuBorel:=borel_regular_restrict_borel hH hHBorel hWBorel.
have hMuFinite:mu setT < +oo by rewrite /mu /measure_restrict setIT; exact hRect.2.
have hVitali:=euclidean_finite_measure_centered_vitali hMu hMuBorel hMuFinite.
pose Good:set X:=[set w|upper_metric_density m mu w= 1].
pose Z:=W `&` Good.
have hOutside:mu (W `\` Z)=0.
  have hSubset:W `\` Z `<=` W by move=>x hx; exact hx.1.
  rewrite /mu (measure_restrict_subset_value H hSubset).
  have hSets:W `\` Z=W `\` Good.
    apply/seteqP; split.
    - move=>x [hw hn]; split; first exact hw; move=>hg; exact:hn (conj hw hg).
    - move=>x [hw hn]; split; first exact hw; by move=>[_ hg]; exact:hn hg.
  rewrite hSets; exact:uniform_compact_chart_upper_density_one hChart.
pose J:=open_convex_euclidean_sets R n.
pose S:=fun j:J=>val j.
pose c:=fun j:J=>@integral_geometric_gauge R n m hmn t (val j).
have hc j:0<=c j.
  exact:(@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)
    (metric_borel_suslin (open_borel_set (set_valP j).1))).
have hEmpty:@is_inner_convex R (R_n R n) (@set0 X) by move=>x y [].
pose j0:J:=@exist _ (fun U=>U \in [set U:set X|open U /\@is_inner_convex R (R_n R n) U])
  set0 (mem_set (conj open0 hEmpty)).
have hLocalEstimate d:(0<d)%R ->Q W<=((1+d)^+2)%R%:E*H W.
  move=>hd.
  apply:(caratheodory_limit_least (@convex_integral_geometric_measure_specification R n m hmn t))
    =>delta nu hDelta hNu.
  have [k hk]:=reciprocal_metric_cutoffs_cofinal hDelta.
  pose cutoff:R:=(((k.+1)%:R)^-1)%R.
  have hCutoff:(0<cutoff)%R by rewrite /cutoff invr_gt0 ltr0n.
  have hNuMeasure:=metric_scale_envelope_is_measure hNu hc.
  have hNull A:A `<=` W ->mu A=0 ->nu A=0.
    move=>hAW hZero.
    have hHZero:H A=0 by rewrite /mu (measure_restrict_subset_value H hAW) in hZero.
    have hQZero:=@convex_integral_geometric_hausdorff_null R n m hmn t A ht hHZero.
    have hBound:=@caratheodory_limit_upper R X J S c Q
      (@convex_integral_geometric_measure_specification R n m hmn t) A delta nu hDelta hNu.
    change (Q A=0) in hQZero.
    change (is_true (nu A<=Q A)) in hBound.
    rewrite hQZero in hBound.
    apply/eqP; rewrite eq_le hBound /=.
    exact:(@measure_nonnegative R (Choice.clone X _) nu hNuMeasure A).
  have hDensity w:Z w ->upper_metric_density m mu w= 1 by move=>[_ hg].
  have hLocal w:Z w ->exists s:R,(0<s)%R /\forall r:R,(0<r<s)%R ->exists j:J,
      W `&` @MetricClosedBalls.metric_closed_ball R X w r `<=` S j /\
      @MetricDiameter.extended_metric_diameter R X (S j)<=(r*3)%R%:E /\
      c j<=((1+d)*EuclideanBallVolume.euclidean_unit_ball_volume R m*r^+m)%R%:E.
    move=>[hw _].
    have [s [hs hCovers]]:=@uniform_compact_chart_local_convex_covers R m n hmn lambda K psi w t d
      hLambda hChart hw ht hd.
    exists s; split; first exact hs; move=>r hRadius.
    have [U [hOpen [hConv [hCover [hDiam hCost]]]]]:=hCovers r hRadius.
    pose j:J:=@exist _ (fun B=>B \in [set B:set X|open B /\@is_inner_convex R (R_n R n) B])
      U (mem_set (conj hOpen hConv)).
    exists j; by split; last split.
  have hBound:=@metric_density_convex_cover_cutoff_bound R X m J j0 S c delta cutoff d
    mu nu W Z hMu hMuBorel hVitali hNu hc hCutoff hk hd hOutside hNull hDensity hLocal.
  by rewrite /mu /measure_restrict setIT in hBound.
apply:(@extended_power_geometric_squeeze R (H W) (Q W) 2%N (measure_nonnegative hH W)).
move=>b hb.
have hd:(0<b-1)%R by rewrite subr_gt0.
have hBound:=hLocalEstimate (b-1)%R hd.
have hShift:(1+(b-1)=b)%R by ring.
by rewrite hShift in hBound.
Qed.
