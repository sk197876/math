(** Federer (1969), 2.10.13, p. 177, last proof paragraph: the measure
    induced by the monotone arc-length parameter s equals the image-cost
    measure psi of 2.10.10, p. 176. Identify them by interval increments and
    Borel regularity, using 2.10.7, pp. 174–175. These support, rather than
    state, the present curve identification. No relevant correction occurs
    in the local Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength CurveOneSidedLimits
  CurveDiscontinuities CurveImageMeasureLower CurveImageMeasureUpper StieltjesContinuityPoints
  StieltjesCaratheodory StieltjesCaratheodoryConsequences StieltjesCaratheodoryIdentification
  StieltjesIntervalUniqueness BorelImageCoverCost BorelCaratheodoryMeasure HausdorffLength
  MeasureUP MeasureBasic BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_curve_arc_length_continuous]: supporting
    continuity of s in 2.10.13, p. 177, from the jump
    identities of 2.5.16, p. 109. Given continuity of g,
    its one-sided limits are already supplied; completeness of
    the metric target is unnecessary for this implication. *)
Lemma continuous_curve_arc_length_continuous (R : realType) (Y : metricType R)
    (g : R -> Y) : curve_locally_finite_variation g ->
  continuous (g : real_line_metric R -> Y) -> continuous (arc_length g).
Proof.
move=> hg hc x.
have [hl hr] := (left_right_continuousP g x).2 (hc x).
apply/left_right_continuousP; split.
- apply/(@arc_length_left_continuous_iff R Y g hg x).
  have h := @curve_left_jump_ge R Y g hg x (g x) hl.
  rewrite mdistxx subr_le0 in h.
  apply/le_anti; by rewrite h (arc_length_left_le hg x).
- apply/(@arc_length_right_continuous_iff R Y g hg x).
  have h := @curve_right_jump_ge R Y g hg x (g x) hr.
  rewrite mdistxx subr_le0 in h.
  apply/le_anti; by rewrite h (arc_length_right_ge hg x).
Qed.

(** Source for [continuous_curve_arc_length_image_measure]: direct
    equality of the two actual measures in the last proof paragraph
    of 2.10.13, p. 177. Equality holds on all subsets by
    the Borel-regular uniqueness law; it is not an assumed
    representation or merely an interval-value specification. *)
Theorem continuous_curve_arc_length_image_measure (R : realType) (Y : metricType R)
    (g : R -> Y) : curve_locally_finite_variation g ->
  continuous (g : real_line_metric R -> Y) ->
  @borel_caratheodory_measure R [the metricType R of real_line_metric R]
    (borel_image_cover_cost g (@hausdorff_length R Y))=
    stieltjes_caratheodory_measure (arc_length g).
Proof.
move=> hg hc.
pose c := borel_image_cover_cost g (@hausdorff_length R Y).
pose mu := @borel_caratheodory_measure R [the metricType R of real_line_metric R] c.
pose s := arc_length g.
have hcost := @borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
  (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y).
have hm := @borel_caratheodory_is_measure R [the metricType R of real_line_metric R] c hcost.
have hrm := @borel_caratheodory_borel_regular R [the metricType R of real_line_metric R] c hcost.
have hs := @arc_length_monotone R Y g hg.
have hn := stieltjes_caratheodory_is_measure hs.
have hrn := stieltjes_caratheodory_borel_regular hs.
have hbound a b : (a<b)%R -> mu `]a,b[<=(s b-s a)%:E.
  move=> hab; rewrite (@arc_length_increment R Y g hg a b (ltW hab)).
  exact: curve_image_measure_open_interval_upper hg hab.
have heq a b : (a<b)%R -> s @ a --> s a -> s @ b --> s b ->
    mu `]a,b[=stieltjes_caratheodory_measure s `]a,b[.
  move=> hab ha hb.
  rewrite (stieltjes_caratheodory_open_interval hs hab ha hb).
  apply/eqP; rewrite eq_le (hbound a b hab) /=.
  rewrite (@arc_length_increment R Y g hg a b (ltW hab)).
  exact: continuous_curve_variation_image_measure_lower hc.
apply/funext=> A.
exact: (@stieltjes_continuity_interval_measure_unique R s mu (stieltjes_caratheodory_measure s)
  hm hn hs hrm hrn hbound (fun a b hab => stieltjes_caratheodory_interval_bound hs hab)
  (fun x _ => @curve_image_measure_singleton_null R Y g x)
  (fun x hx => stieltjes_caratheodory_continuity_point_null hs hx) heq A).
Qed.
