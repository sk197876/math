(** Federer (1969), 3.2.6, pp. 245–246: identify the
    actual speed density with the image-cost measure of 2.10.13.
    This supporting equality makes the null and Borel reductions
    independent of a choice of Lipschitz representatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LocallyAbsolutelyContinuousCurve EuclideanCurveSpeedMeasure CurveArcLength CurveVariationUP
  StieltjesMonotone StieltjesIntervalUniqueness StieltjesContinuityPoints
  CurveImageMeasureLower CurveImageMeasureUpper BorelImageCoverCost BorelCaratheodoryMeasure
  CaratheodoryBorelRegular HausdorffLength MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureDensityNullSets LebesgueScalarMeasure RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_speed_measure_singleton]: null
    endpoints in the use of 2.10.13 in Federer 3.2.6,
    p. 246. Absolute continuity makes the speed density
    absolutely continuous with respect to scalar Lebesgue measure. *)
Lemma euclidean_curve_speed_measure_singleton (R:realType) n (f:R->R_n R n) x:
  euclidean_curve_speed_measure f [set x]=0.
Proof.
exact (@measure_density_null_set R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (euclidean_curve_speed_measure f) (lebesgue_scalar_is_measure R)
  (euclidean_curve_speed f) [set x] (euclidean_curve_speed_measure_laws f) (lebesgue_scalar_singleton x)).
Qed.

(** Source for [euclidean_curve_speed_image_measure]: supporting
    equality of measures in the proof of Federer 3.2.6,
    p. 246, by the interval identification of 2.10.13,
    p. 177. Both measures are independently specified; their
    equality on all sets follows from proved Borel regularity. *)
Theorem euclidean_curve_speed_image_measure (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)):
  is_locally_absolutely_continuous_curve f ->
  euclidean_curve_speed_measure f=
    @borel_caratheodory_measure R [the metricType R of real_line_metric R]
      (borel_image_cover_cost f (@hausdorff_length R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])).
Proof.
move=>hAC.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose nu:=euclidean_curve_speed_measure f.
pose c:=borel_image_cover_cost f (@hausdorff_length R [the metricType R of Y]).
pose mu:=@borel_caratheodory_measure R [the metricType R of real_line_metric R] c.
have hCost:=@borel_image_cover_cost_laws R [the topologicalType of real_line_metric R]
  Y f (@hausdorff_length R [the metricType R of Y]) (@hausdorff_length_is_measure R [the metricType R of Y]).
have hm:=borel_caratheodory_is_measure hCost.
have hrm:=borel_caratheodory_borel_regular hCost.
have hn:=euclidean_curve_speed_measure_is_measure hAC.
have hrn:=euclidean_curve_speed_measure_borel_regular hAC.
have hBV:=locally_absolutely_continuous_curve_finite_variation hAC.
have hCont:=locally_absolutely_continuous_curve_continuous hAC.
have hNPoint x:nu [set x]=0:=euclidean_curve_speed_measure_singleton f x.
have hMPoint x:mu [set x]=0:=@curve_image_measure_singleton_null R [the metricType R of Y] f x.
have hNOpen a b:(a<b)%R -> nu `]a,b[=curve_variation f a b.
  move=>hab; rewrite -(@measure_segment_open_interval R nu a b hn (hNPoint a) (hNPoint b)).
  exact (euclidean_curve_speed_measure_interval hAC hab).
have hMOpen a b:(a<b)%R -> mu `]a,b[=curve_variation f a b.
  move=>hab; rewrite -(@measure_segment_open_interval R mu a b hm (hMPoint a) (hMPoint b)).
  exact (continuous_bv_curve_image_measure_interval hBV hCont hab).
have hs a b:(a<=b)%R -> (arc_length f a<=arc_length f b)%R:=@arc_length_monotone R [the metricType R of Y] f hBV a b.
apply:funext=>A.
apply:(@stieltjes_continuity_interval_measure_unique R (arc_length f) nu mu hn hm hs hrn hrm).
- move=>a b hab; rewrite hNOpen //.
  by rewrite (@arc_length_increment R [the metricType R of Y] f hBV a b (ltW hab)).
- move=>a b hab; rewrite hMOpen //.
  by rewrite (@arc_length_increment R [the metricType R of Y] f hBV a b (ltW hab)).
- by move=>x _; exact (hNPoint x).
- by move=>x _; exact (hMPoint x).
- by move=>a b hab _ _; rewrite hNOpen // hMOpen.
Qed.
