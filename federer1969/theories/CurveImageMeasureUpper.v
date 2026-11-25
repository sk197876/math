(** Federer (1969), 2.10.13, p. 177: the arc-length factor gives the upper
    estimate, and the resulting image-cost measure agrees with variation on
    intervals. Use the factor to bound interval image costs, then subdivide
    source intervals at null endpoints as in 2.10.7, p. 174. This replaces
    the printed exceptional-fibre comparison by covering-measure
    inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology num_normedtype.
From Federer Require Import IntervalBumpFunctions RealMetricBackground HausdorffLength CurveVariationUP CurveArcLength CurveImageLengthBound
  CurveImageMeasureLower StieltjesCaratheodoryUP StieltjesIntervalBounds MonotoneIntervalSubdivision
  StieltjesContinuityPoints MeasureUP MeasureBasic BorelCoverCostUP BorelImageCoverCost
  BorelCaratheodoryMeasure TopologicalBorel MetricDiameter MetricScaleEnvelopeUP
  MetricScaleCutoffCost MetricScaleWeightedBound CaratheodoryLimitUP CaratheodoryBorelRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_open_interval_image_length_bound]: supporting
    interval image-cost estimate from the arc-length factor in
    2.10.13, p. 177. The open interval is contained in its
    closed segment; continuity is not required for this inequality. *)
Lemma curve_open_interval_image_length_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g -> (a<=b)%R ->
  @hausdorff_length R Y (g @` `]a,b[)<=curve_variation g a b.
Proof.
move=> hg hab.
apply: le_trans (_ : hausdorff_length (g @` `[a,b])<=_); last exact: curve_segment_image_length_bound hg hab.
apply: (@measure_mono R Y _ (@hausdorff_length_is_measure R Y))=> y [x hx <-].
exists x=> //; move: hx; rewrite /= !in_itv /= => /andP[ha hb].
by rewrite (ltW ha) (ltW hb).
Qed.

(** Source for [curve_image_measure_open_interval_upper]: supporting
    upper variation estimate of 2.10.13, p. 177. At each
    source cutoff, sufficiently short Borel intervals have cost
    at most their arc-length increment. Subdivide to all bounded
    intervals and take the supremum of cutoff measures. *)
Theorem curve_image_measure_open_interval_upper (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g -> (a<b)%R ->
  @borel_caratheodory_measure R [the metricType R of real_line_metric R] (borel_image_cover_cost g (@hausdorff_length R Y)) `]a,b[
    <=curve_variation g a b.
Proof.
move=> hg hab.
pose c := borel_image_cover_cost g (@hausdorff_length R Y).
have hc := @borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y).
rewrite -(@arc_length_increment R Y g hg a b (ltW hab)).
apply: (caratheodory_limit_least (@borel_caratheodory_specification R [the metricType R of real_line_metric R] c))=> delta nu hd hn.
have hm := metric_scale_envelope_is_measure hn
  (fun j => borel_cover_cost_nonnegative hc (set_valP j)).
have hz x : nu [set x]=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm _) andbT.
  have hb := @caratheodory_limit_upper R [the metricType R of real_line_metric R]
    _ _ _ _ (@borel_caratheodory_specification R [the metricType R of real_line_metric R] c) [set x] delta nu hd hn.
  by rewrite (@curve_image_measure_singleton_null R Y g x) in hb.
have [k hk] := reciprocal_metric_cutoffs_cofinal hd.
pose d : R := (((k.+1)%:R)^-1)%R.
have hdpos : (0<d)%R by rewrite /d invr_gt0 ltr0n.
refine (@interval_increment_subdivision_bound R (arc_length g) nu hm set0 d (countable0 R) hdpos
  (fun x _ => hz x) _ a b hab).
move=> u v huv hshort.
have hB : borel_set (`]u,v[ : set (real_line_metric R)).
  apply: open_borel_set; exact: interval_open.
pose j : @borel_metric_sets R [the metricType R of real_line_metric R] :=
  Sub `]u,v[ (mem_set hB).
have hdiam : extended_metric_diameter (val j)<=delta.
  apply: le_trans (@stieltjes_interval_diameter_bound R (stieltjes_interval_index huv)) _.
  apply: le_trans (_ : d%:E<=delta); last exact hk.
  rewrite lee_fin; exact: ltW hshort.
have hb := @metric_scale_generator_bound R [the metricType R of real_line_metric R]
  _ _ _ delta nu j hn (borel_cover_cost_nonnegative hc (set_valP j)) hdiam.
apply: le_trans hb _.
rewrite (@arc_length_increment R Y g hg u v (ltW huv)).
exact: curve_open_interval_image_length_bound hg (ltW huv).
Qed.

(** Source for [continuous_bv_curve_image_measure_interval]: direct
    identification of variation with the interval value of the
    image-cost construction in 2.10.13, p. 177. The displayed
    equality of measures in the last proof paragraph is proved
    later from these interval values. No completeness of Y is needed. *)
Theorem continuous_bv_curve_image_measure_interval (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g ->
  continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  @borel_caratheodory_measure R [the metricType R of real_line_metric R] (borel_image_cover_cost g (@hausdorff_length R Y)) `[a,b]
    =curve_variation g a b.
Proof.
move=> hg hc hab.
have hm := borel_caratheodory_is_measure
  (@borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y)).
rewrite (@measure_segment_open_interval R _ a b hm
  (@curve_image_measure_singleton_null R Y g a) (@curve_image_measure_singleton_null R Y g b)).
apply/eqP; rewrite eq_le (curve_image_measure_open_interval_upper hg hab) /=.
exact: continuous_curve_variation_image_measure_lower hc.
Qed.
