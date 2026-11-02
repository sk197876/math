(** Supporting Federer (1969), 2.10.14, p. 177: for a locally BV curve the
    image-cost measure is bounded by the measure induced by its arc length.
    Interval image costs are bounded by variation, so the covering infimum
    for 2.10.7, p. 174, dominates them. This extends the upper comparison
    used in the proof of 2.10.13, p. 177, to discontinuous curves. they do
    not state this combined comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  CurveImageMeasureUpper MetricCurveLocalization StieltjesSubstitution CurveJumpLocalization
  HausdorffLength BorelImageCoverCost BorelCoverCostUP BorelCaratheodoryMeasure
  MeasureUP MeasureBasic StieltjesCaratheodoryUP StieltjesCaratheodory
  StieltjesIntervalBounds StieltjesCaratheodoryConsequences MetricScaleMeasureBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bv_curve_image_measure_below_arc_length]: supporting
    diffuse-measure upper bound for 2.10.14, p. 177.
    Continuity and completeness of the target are unnecessary. *)
Theorem bv_curve_image_measure_below_arc_length (R : realType) (Y : metricType R)
    (g : R -> Y) : curve_locally_finite_variation g -> forall A,
  @borel_caratheodory_measure R [the metricType R of real_line_metric R]
    (borel_image_cover_cost g (@hausdorff_length R Y)) A<=
    stieltjes_caratheodory_measure (arc_length g) A.
Proof.
move=> hg A.
pose mu := @borel_caratheodory_measure R [the metricType R of real_line_metric R]
  (borel_image_cover_cost g (@hausdorff_length R Y)).
have hm := @borel_caratheodory_is_measure R [the metricType R of real_line_metric R] _
  (@borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y)).
pose nu := stieltjes_caratheodory_scale (arc_length g) 1.
have hn := stieltjes_caratheodory_scale_specification (arc_length g) 1.
have hb : mu A<=nu A.
  apply: (@measure_bounded_by_metric_scale_envelope R [the metricType R of real_line_metric R]
    _ _ _ 1 nu mu hn hm)=> j _.
  have hj := set_valP j.
  have hlt : ((val j).1<(val j).2)%R := hj.
  rewrite /stieltjes_interval_cost (arc_length_increment hg (ltW hlt)).
  exact: curve_image_measure_open_interval_upper hg hlt.
apply: le_trans hb _.
exact: (@caratheodory_limit_upper R [the metricType R of real_line_metric R]
  _ _ _ _ (stieltjes_caratheodory_specification (arc_length g)) A 1 nu lte01 hn).
Qed.

(** Source for [retracted_arc_length_segment_upper]: supporting
    total-mass bound in 2.10.14, p. 177. Enclose [a,b]
    in (a-1,b+1); the retracted curve has no additional
    variation in the constant tails. This includes both endpoint atoms. *)
Theorem retracted_arc_length_segment_upper (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R -> curve_variation g a b< +oo ->
  stieltjes_caratheodory_measure (arc_length (g \o @segment_retraction R a b)) `[a,b]
    <=curve_variation g a b.
Proof.
move=> hab hfin.
pose h := g \o @segment_retraction R a b.
have hh := @metric_finite_interval_retracted_variation R Y g a b hab hfin.
have hs := @arc_length_monotone R Y h hh.
have hm := stieltjes_caratheodory_is_measure hs.
have huv : (a-1<b+1)%R by lra.
have hsub : (`[a,b] : set (real_line_metric R)) `<=` `](a-1)%R,(b+1)%R[.
  move=> x; rewrite /= !in_itv /= => /andP[ha hb]; apply/andP; split; lra.
apply: le_trans (measure_mono hm hsub) _.
apply: le_trans (stieltjes_caratheodory_interval_bound hs huv) _.
rewrite (@arc_length_increment R Y h hh _ _ (ltW huv)).
have hra : @segment_retraction R a b (a-1)%R=a.
  apply: segment_retraction_below=> //; lra.
have hrb : @segment_retraction R a b (b+1)%R=b.
  apply: segment_retraction_above=> //; lra.
have hbnd := @metric_variation_reparametrization_bound R Y g
  (@segment_retraction R a b) (a-1)%R (b+1)%R
  (@segment_retraction_monotone R a b) (ltW huv).
by rewrite hra hrb in hbnd.
Qed.
