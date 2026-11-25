(** Federer (1969), 2.10.14, p. 177: arbitrary metric curves have variation
    equal to the upper multiplicity integral plus their two one-sided
    upper-limit jump sums. The May 1987 erratum, p. 3, book p. 177 line 23,
    explicitly replaces the printed integral by the upper integral. No
    finite-variation, measurability, or target-completeness hypothesis is
    added. The book omits the proof. Here endpoint distance is covered by
    the scalar distance image and oriented jump bridges; the reverse
    inequality separates the atoms of the arc-length measure. Erratum p. 3,
    book p. 177 line 27, changes [F11] to [F12] in the separate
    bibliographic sentence about light continuous maps; that sentence is not
    an additional numbered theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP MetricCurveLocalization
  StieltjesSubstitution CurveJumpBudget RetractedCurveJumpBudget CurveJumpVariationLower
  CurveJumpVariationUpper CurveUpperMultiplicity MeasureUP MeasureBasic
  BorelImageCoverCost BorelCaratheodoryMeasure HausdorffLength HausdorffMeasure
  HausdorffLengthCompatibility ExtendedRealOrderTopology PartialFunctionBasic
  MeasureIntegralBounds MappingMultiplicity CurveOneSidedJumpUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_curve_variation_jump_formula]: direct
    equality in 2.10.14, p. 177, with the upper integral
    required by erratum p. 3, book p. 177 line 23.
    Both sides may be infinite. The actual upper limits and
    numerical sums have been defined independently of variation. *)
Theorem metric_curve_variation_jump_formula (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<b)%R ->
  curve_variation g a b=curve_upper_multiplicity_integral g a b+
    curve_interval_jump_budget g a b.
Proof.
move=> hab; have habW := ltW hab.
apply/eqP; rewrite eq_le; apply/andP; split.
- case: (ltP (curve_interval_jump_budget g a b) +oo)=> hJ.
  + pose h := g \o @segment_retraction R a b.
    have hglobal : curve_jump_measure h true setT+curve_jump_measure h false setT< +oo.
      by rewrite /h (@curve_interval_jump_budget_retracted_global R Y g a b habW).
    have heV : curve_variation g a b=curve_variation h a b.
      apply: metric_curve_variation_equal_on=> x hx.
      by rewrite /h /= (@segment_retraction_id R a b x hx).
    rewrite heV (finite_jump_budget_upper_multiplicity_image_measure habW hJ).
    rewrite -(@curve_interval_jump_budget_retracted R Y g a b habW).
    have hb := @finite_jump_curve_variation_image_measure_lower R Y h a b hglobal.
    apply: le_trans hb _; apply: leeD; last exact: lexx.
    have hm := @borel_caratheodory_is_measure R [the metricType R of real_line_metric R] _
      (@borel_image_cover_cost_laws R [the topologicalType of real_line_metric R]
        Y h (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y)).
    apply: (measure_mono hm)=> x.
    rewrite /= !in_itv /= => /andP[ha hb']; by rewrite (ltW ha) (ltW hb').
  + have he : curve_interval_jump_budget g a b=+oo.
      apply/eqP; by rewrite eq_le leey hJ.
    have hnot : curve_upper_multiplicity_integral g a b!=-oo.
      apply/eqP=> hbad.
      have hh := curve_upper_multiplicity_integral_nonnegative g a b.
      by rewrite hbad in hh.
    by rewrite he addey // leey.
- case: (ltP (curve_variation g a b) +oo)=> hV.
  + have hglobal := @finite_variation_global_retracted_jump_budget R Y g a b habW hV.
    have hJ : curve_interval_jump_budget g a b< +oo.
      by rewrite (@curve_interval_jump_budget_retracted_global R Y g a b habW) in hglobal.
    rewrite (finite_jump_budget_upper_multiplicity_image_measure habW hJ).
    exact: finite_variation_retracted_image_jump_upper habW hV.
  + have he : curve_variation g a b=+oo.
      apply/eqP; by rewrite eq_le leey hV.
    by rewrite he leey.
Qed.

(** Source for [federer_2_10_14]: direct corrected displayed formula
    of 2.10.14, p. 177. The H1 normalisation is that
    of 2.10.2, p. 171; the right sum runs over [a,b),
    the left sum over (a,b], and the integral is upper
    as corrected in erratum p. 3, book p. 177 line 23. *)
Theorem federer_2_10_14 (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : (a<b)%R ->
  curve_variation g a b=
    measure_upper_integral (@hausdorff_measure R Y 1)
      (partial_function_total (fun y => (@mapping_multiplicity R
        [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R)))+
    nonnegative_sum (`[a,b[ : set (real_line_metric R)) (curve_right_jump_size g)+
    nonnegative_sum (`]a,b] : set (real_line_metric R)) (curve_left_jump_size g).
Proof.
move=> hab.
have he : @hausdorff_measure R Y 1=@hausdorff_length R Y.
  by apply/funext=> A; exact: hausdorff_measure_one_length.
rewrite he.
have hh := @metric_curve_variation_jump_formula R Y g a b hab.
rewrite /curve_upper_multiplicity_integral /curve_interval_jump_budget
  !curve_jump_measure_sum addeA in hh.
exact: hh.
Qed.
