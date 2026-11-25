(** Federer (1969), 2.10.14, p. 177: the counting multiplicity is integrated
    with the upper integral, as corrected by the May 1987 erratum, p. 3,
    book p. 177 line 23. A finite jump budget implies countably many
    discontinuities; in that case the integrand is measurable and its actual
    integral is the image-cost measure of 2.10.10, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import IntervalBumpFunctions RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureUpperIntegralNonnegative
  HausdorffLength BorelRegularMeasureUP TopologicalBorel BorelImageCoverCost
  BorelCaratheodoryMeasure MappingMultiplicity CurveLengthMultiplicity
  CurveJumpBudget RetractedCurveJumpBudget CountablyDiscontinuousImages StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_upper_multiplicity_integral]: direct upper
    integral of N(g|[a,b],y) against H1 in 2.10.14,
    p. 177, with the erratum p. 3, book p. 177 line 23.
    No measurability, continuity or finite variation is assumed. *)
Definition curve_upper_multiplicity_integral (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) :=
  measure_upper_integral (@hausdorff_length R Y)
    (partial_function_total (fun y => (@mapping_multiplicity R
      [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R))).

(** Source for [curve_upper_multiplicity_integral_nonnegative]:
    supporting nonnegativity in 2.10.14, p. 177, from
    2.4.3(3), p. 82, valid also for nonmeasurable multiplicity. *)
Lemma curve_upper_multiplicity_integral_nonnegative (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : 0<=curve_upper_multiplicity_integral g a b.
Proof.
apply: (@measure_upper_integral_nonnegative R Y _ (@hausdorff_length_is_measure R Y)).
apply: (@measure_almost_everywhere_mono R Y _ (@hausdorff_length_is_measure R Y)
  setT _ _ (@measure_almost_everywhere_true R Y _ (@hausdorff_length_is_measure R Y))).
move=> y hy; exists (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g `[a,b] y).
split; first by [].
exact: mapping_multiplicity_nonnegative.
Qed.

(** Source for [finite_jump_budget_upper_multiplicity_image_measure]:
    supporting actual-integral case of 2.10.14, p. 177.
    Retract to [a,b], prove countable discontinuities from the
    actual jump sums, and apply 2.10.10; the restricted fibres
    of the original and representative maps agree exactly. *)
Theorem finite_jump_budget_upper_multiplicity_image_measure (R : realType)
    (Y : metricType R) (g : R -> Y) (a b : R) : (a<=b)%R ->
  curve_interval_jump_budget g a b< +oo ->
  curve_upper_multiplicity_integral g a b=
    @borel_caratheodory_measure R [the metricType R of real_line_metric R]
      (borel_image_cover_cost (g \o @segment_retraction R a b) (@hausdorff_length R Y)) `[a,b].
Proof.
move=> hab hJ.
pose h := g \o @segment_retraction R a b.
have hglobal : curve_jump_measure h true setT+curve_jump_measure h false setT< +oo.
  by rewrite /h (@curve_interval_jump_budget_retracted_global R Y g a b hab).
have hD := finite_global_jump_budget_countable hglobal.
have hc x : ~curve_jump_exception_set h x -> h @ x --> h x.
  exact: curve_continuous_off_jump_exception_set.
have hclosed C : closed C -> measure_measurable (@hausdorff_length R Y) C.
  move=> hC; apply: (borel_regular_borel_measurable (@hausdorff_length_is_measure R Y)
    (@hausdorff_length_borel_regular R Y)); exact: closed_borel_set hC.
have hi := @countably_discontinuous_multiplicity_integral R Y h (@hausdorff_length R Y)
  (curve_jump_exception_set h) `[a,b] (@hausdorff_length_is_measure R Y)
  hclosed hD hc (closed_borel_set (@segment_closed_real R a b)).
have he y := @mapping_multiplicity_equal_on R [the choiceType of real_line_metric R] Y
  g h `[a,b] (fun x hx => congr1 g (esym (@segment_retraction_id R a b x hx))) y.
have hf : (fun y => (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R))=
    (fun y => (@mapping_multiplicity R [the choiceType of real_line_metric R] Y h `[a,b] y : extended_real_line R)).
  by apply/funext=> y; exact: he.
rewrite /curve_upper_multiplicity_integral hf.
exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
Qed.
