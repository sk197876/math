(** Federer (1969), 2.10.13, p. 177, first assertion: the variation of a
    continuous metric curve on [a,b] is the integral of its counting
    multiplicity against H1. Use 2.10.10 and the image-cost interval
    identity. Localise a finite-variation interval by the segment
    retraction; retain infinite variation by the lower estimate. The
    arc-length image bound and source subdivision replace the printed
    comparison of fibres outside countably many plateau values. No relevant
    Federer erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import IntervalBumpFunctions RealMetricBackground RealMetricCompleteness RealLineSeparability
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP
  BorelRegularMeasureUP TopologicalBorel BorelImageMeasurability BorelImageCoverCost
  BorelCaratheodoryMeasure BorelMultiplicityIntegral MappingMultiplicity
  HausdorffLength HausdorffLengthCompatibility HausdorffMeasure CountingMeasure CurveArcLength CurveVariationUP
  MetricCurveLocalization StieltjesSubstitution CurveImageMeasureLower CurveImageMeasureUpper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_multiplicity_equal_on]: supporting locality
    of N(g|A,y) in 2.10.13, p. 177. Maps agreeing on A
    have exactly the same fibres, including infinite fibres. *)
Lemma mapping_multiplicity_equal_on (R : realType) (X : choiceType) (Y : Type)
    (g h : X -> Y) (A : set X) : (forall x, A x -> g x=h x) ->
  forall y, @mapping_multiplicity R X Y g A y=@mapping_multiplicity R X Y h A y.
Proof.
move=> he y; rewrite /mapping_multiplicity; congr (counting_measure _).
apply/seteqP; split=> x [hx hy]; split=> //.
- by rewrite -(he x hx).
- by rewrite (he x hx).
Qed.

(** Source for [continuous_curve_multiplicity_image_measure]: supporting
    application of 2.10.10, p. 176, in 2.10.13, p. 177.
    Continuous Borel images are H1 measurable by 2.2.13,
    pp. 69–70; no completeness of the metric target is needed. *)
Lemma continuous_curve_multiplicity_image_measure (R : realType) (Y : metricType R)
    (g : R -> Y) (A : set (real_line_metric R)) :
  continuous (g : real_line_metric R -> Y) -> borel_set A ->
  is_measure_integral (@hausdorff_length R Y)
    (partial_function_total (fun y =>
      (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g A y : extended_real_line R)))
    (@borel_caratheodory_measure R [the metricType R of real_line_metric R]
      (borel_image_cover_cost g (@hausdorff_length R Y)) A).
Proof.
move=> hg hA; have [D [hD hden]] := real_line_countable_dense R.
have hb := @hausdorff_length_is_measure R Y.
have hr := @hausdorff_length_borel_regular R Y.
apply: (@borel_multiplicity_integral R [the metricType R of real_line_metric R] Y g
  (@hausdorff_length R Y) hb D A hD hden _ hA).
move=> B hB.
exact: (@continuous_borel_image_measurable R [the metricType R of real_line_metric R] Y g
  (@hausdorff_length R Y) hb B (@real_line_metric_complete R)
  (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y) hg
  (fun C hC => @borel_regular_borel_measurable R Y _ hb hr C (closed_borel_set hC)) hB).
Qed.

(** Source for [continuous_curve_length_multiplicity]: direct
    first formula of 2.10.13, p. 177, using the legacy
    H1 interface. The actual integral exists, also for infinite
    variation and noninjective curves. Finite variation is assumed
    only on [a,b] inside the finite branch of the proof. *)
Theorem continuous_curve_length_multiplicity (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  is_measure_integral (@hausdorff_length R Y)
    (partial_function_total (fun y =>
      (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R)))
    (curve_variation g a b).
Proof.
move=> hg hab.
case: (ltP (curve_variation g a b) +oo)=> [hfin|hinf].
- pose r := @segment_retraction R a b.
  pose h := g \o r.
  have hh : curve_locally_finite_variation h.
    exact: metric_finite_interval_retracted_variation (ltW hab) hfin.
  have hc : continuous (h : real_line_metric R -> Y).
    exact: metric_retracted_curve_continuous hg.
  have he x : (a<=x<=b)%R -> h x=g x.
    by move=> hx; rewrite /h /r /= segment_retraction_id.
  have hv : curve_variation h a b=curve_variation g a b.
    exact: metric_curve_variation_equal_on he.
  have hi := @continuous_curve_multiplicity_image_measure R Y h `[a,b] hc
    (closed_borel_set (@segment_closed_real R a b)).
  rewrite (@continuous_bv_curve_image_measure_interval R Y h a b hh hc hab) hv in hi.
  have hf : (fun y => (@mapping_multiplicity R [the choiceType of real_line_metric R] Y h `[a,b] y : extended_real_line R))=
      (fun y => (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R)).
    apply/funext=> y; apply: mapping_multiplicity_equal_on=> x hx.
    apply: he; by move: hx; rewrite /= in_itv /=.
  by rewrite hf in hi.
- pose c := borel_image_cover_cost g (@hausdorff_length R Y).
  pose mu := @borel_caratheodory_measure R [the metricType R of real_line_metric R] c.
  have hm := borel_caratheodory_is_measure
    (@borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y g
      (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y)).
  have hl := @continuous_curve_variation_image_measure_lower R Y g a b hg.
  have hsub : (`]a,b[ : set (real_line_metric R)) `<=` `[a,b].
    move=> x; rewrite /= !in_itv /= => /andP[ha hb]; by rewrite (ltW ha) (ltW hb).
  have hb := le_trans hl (@measure_mono R [the choiceType of real_line_metric R] mu hm _ _ hsub).
  have hv : curve_variation g a b=mu `[a,b].
    apply/eqP; rewrite eq_le hb /=; exact: le_trans (leey _) hinf.
  rewrite hv; exact: continuous_curve_multiplicity_image_measure hg
    (closed_borel_set (@segment_closed_real R a b)).
Qed.

(** Source for [federer_2_10_13_length]: direct first assertion
    of Federer 2.10.13, p. 177, for the current normalized
    H1 measure of 2.10.2(1), p. 171. Both interval endpoints
    are retained, and no finiteness assumption is added. *)
Corollary federer_2_10_13_length (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  is_measure_integral (@hausdorff_measure R Y 1)
    (partial_function_total (fun y =>
      (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R)))
    (curve_variation g a b).
Proof.
move=> hg hab.
have he : @hausdorff_measure R Y 1=@hausdorff_length R Y.
  by apply/funext=> A; exact: hausdorff_measure_one_length.
rewrite he; exact: continuous_curve_length_multiplicity hg hab.
Qed.
