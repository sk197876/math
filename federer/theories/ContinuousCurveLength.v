(** Federer (1969), 2.10.13, p. 177, both assertions. The normalized H1
    multiplicity integral equals variation; finite variation together with
    the null-image condition is equivalent to finite-family absolute
    continuity. The latter proof is metric and therefore strengthens the
    book's reflexive-Banach formulation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureIntegralUP MappingMultiplicity CurveVariationUP MetricCurveAbsoluteContinuityUP
  CurveLengthMultiplicity CurveNullImageCriterion HausdorffLength HausdorffLengthCompatibility
  HausdorffMeasure LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_13]: direct complete conclusion
    of Federer 2.10.13, p. 177. The actual multiplicity
    integral exists, including infinite length. The second assertion
    is strengthened from reflexive Banach targets to all metric
    targets for the existing finite-family definition of absolute
    continuity. Both null-set quantifiers range over arbitrary sets,
    and the finite-variation condition concerns only [a,b]. *)
Theorem federer_2_10_13 (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  is_measure_integral (@hausdorff_measure R Y 1)
    (partial_function_total (fun y =>
      (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g `[a,b] y : extended_real_line R)))
    (curve_variation g a b) /\
  (is_absolutely_continuous_metric_curve g a b <->
    curve_variation g a b < +oo /\
    forall T : set (real_line_metric R), T `<=` `[a,b] -> lebesgue_scalar_measure T=0 ->
      @hausdorff_measure R Y 1 (g @` T)=0).
Proof.
move=> hg hab; split; first exact: federer_2_10_13_length hg hab.
have he : @hausdorff_measure R Y 1=@hausdorff_length R Y.
  by apply/funext=> A; exact: hausdorff_measure_one_length.
rewrite he; exact: continuous_curve_null_image_criterion hg hab.
Qed.
