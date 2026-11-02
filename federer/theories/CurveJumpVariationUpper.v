(** Federer (1969), 2.10.14, p. 177: the upper bound for the image-measure
    contribution plus jumps. For finite variation, the retracted curve has a
    finite arc-length measure on [a,b]; its atoms are the two one-sided
    jumps. Separate those atoms from the image-cost measure, which vanishes
    on countable source sets. The combined argument supplies the proof
    omitted by Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  CurveOneSidedJumpUP CurveJumpBudget CurveJumpArcLength CurveArcLengthAtoms
  CurveDiffuseAtomicBound DiscontinuousCurveMeasureBound MetricCurveLocalization
  RetractedCurveJumpBudget StieltjesSubstitution StieltjesCaratheodory HausdorffLength BorelImageCoverCost
  BorelCaratheodoryMeasure CurveImageMeasureLower MeasureUP MeasureBasic
  NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_interval_jump_budget_atom_bound]: supporting
    bound of the two jump sums in 2.10.14, p. 177,
    by the sum of arc-length atoms on the closed segment.
    At interior points both jumps occur; at each endpoint only
    the inward-facing jump is needed. *)
Lemma curve_interval_jump_budget_atom_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g ->
  curve_interval_jump_budget g a b<=
    nonnegative_sum (`[a,b] : set (real_line_metric R))
      (fun x => stieltjes_caratheodory_measure (arc_length g) [set x]).
Proof.
move=> hg.
have he : nonnegative_sum (`[a,b] : set (real_line_metric R))
    (fun x => stieltjes_caratheodory_measure (arc_length g) [set x])=
    curve_jump_measure g true `[a,b]+curve_jump_measure g false `[a,b].
  rewrite !curve_jump_measure_sum.
  rewrite -nonnegative_sum_add.
  - apply: nonnegative_sum_ext=> x hx; exact: curve_arc_length_atom_jump_sum x hg.
  - move=> x hx; exact: curve_one_sided_jump_nonnegative.
  - move=> x hx; exact: curve_one_sided_jump_nonnegative.
rewrite he; apply: leeD; apply: (measure_mono (curve_jump_measure_is_measure g _))=> x.
- rewrite /= !in_itv /= => /andP[ha hb]; by rewrite ha (ltW hb).
- rewrite /= !in_itv /= => /andP[ha hb]; by rewrite (ltW ha) hb.
Qed.

(** Source for [finite_variation_global_retracted_jump_budget]:
    supporting finite jump-budget consequence in 2.10.14, p. 177.
    Retraction removes the exterior-facing endpoint jumps and all
    jumps outside [a,b], making the global sum finite. *)
Theorem finite_variation_global_retracted_jump_budget (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R -> curve_variation g a b< +oo ->
  curve_jump_measure (g \o @segment_retraction R a b) true setT+
    curve_jump_measure (g \o @segment_retraction R a b) false setT< +oo.
Proof.
move=> hab hfin.
pose h := g \o @segment_retraction R a b.
have hh := @metric_finite_interval_retracted_variation R Y g a b hab hfin.
have hJ := @curve_interval_jump_budget_atom_bound R Y h a b hh.
have hs := @arc_length_monotone R Y h hh.
have hn := stieltjes_caratheodory_is_measure hs.
have hr := stieltjes_caratheodory_borel_regular hs.
have hsum := @metric_singleton_sum_bound R [the metricType R of real_line_metric R]
  _ `[a,b] hn hr.
have htotal := @retracted_arc_length_segment_upper R Y g a b hab hfin.
(* The desired original budget is below the full sum of the two
   retracted atom weights on the closed segment. *)
have hlocal : curve_interval_jump_budget g a b<=curve_interval_jump_budget h a b.
  by rewrite /h (@curve_interval_jump_budget_retracted R Y g a b hab).
rewrite (@curve_right_jump_global_retraction R Y g a b hab)
  (@curve_left_jump_global_retraction R Y g a b hab).
exact: le_lt_trans (le_trans hlocal (le_trans hJ (le_trans hsum htotal))) hfin.
Qed.

(** Source for [finite_variation_retracted_image_jump_upper]:
    supporting upper inequality of 2.10.14, p. 177.
    The diffuse image-cost measure plus the required inward
    jump budget is at most the original finite variation. *)
Theorem finite_variation_retracted_image_jump_upper (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<=b)%R -> curve_variation g a b< +oo ->
  @borel_caratheodory_measure R [the metricType R of real_line_metric R]
    (borel_image_cover_cost (g \o @segment_retraction R a b) (@hausdorff_length R Y)) `[a,b]+
    curve_interval_jump_budget g a b<=curve_variation g a b.
Proof.
move=> hab hfin.
pose h := g \o @segment_retraction R a b.
pose nu := stieltjes_caratheodory_measure (arc_length h).
pose mu := @borel_caratheodory_measure R [the metricType R of real_line_metric R]
  (borel_image_cover_cost h (@hausdorff_length R Y)).
have hh := @metric_finite_interval_retracted_variation R Y g a b hab hfin.
have hs := @arc_length_monotone R Y h hh.
have hn := stieltjes_caratheodory_is_measure hs.
have hr := stieltjes_caratheodory_borel_regular hs.
have hm := @borel_caratheodory_is_measure R [the metricType R of real_line_metric R] _
  (@borel_image_cover_cost_laws R [the topologicalType of real_line_metric R] Y h
    (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y)).
have hcount := finite_global_jump_budget_countable
  (@finite_variation_global_retracted_jump_budget R Y g a b hab hfin).
have hoff x : ~curve_jump_exception_set h x -> nu [set x]=0.
  move=> hx; rewrite /nu (curve_arc_length_atom_jump_sum x hh).
  case: (eqVneq (curve_one_sided_jump h true x+curve_one_sided_jump h false x) 0)=> he; first exact he.
  exfalso; exact: hx he.
have hbound := @metric_diffuse_atomic_sum_bound R [the metricType R of real_line_metric R]
  mu nu `[a,b] (curve_jump_exception_set h) hm hn hr
  (@bv_curve_image_measure_below_arc_length R Y h hh)
  (@curve_image_measure_singleton_null R Y h) hcount hoff.
have hlocal : curve_interval_jump_budget g a b<=curve_interval_jump_budget h a b.
  by rewrite /h (@curve_interval_jump_budget_retracted R Y g a b hab).
have hJ := @curve_interval_jump_budget_atom_bound R Y h a b hh.
apply: le_trans (leeD (lexx _) (le_trans hlocal hJ)) _.
apply: le_trans hbound _; exact: retracted_arc_length_segment_upper hab hfin.
Qed.
