(** Federer (1969), 4.1.9, p. 363: the original
    integral of weighted slice image measures. Its
    independent specification uses Radon laws and the
    literal time integrals of positive compact scalar
    tests. The weighted product image proves existence;
    downstream variation bounds use the opaque public law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentHomotopyUP
  CurrentIntegrationCriterion CurrentHomotopySliceMeasureIntegral CurrentHomotopyCylinder
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  LebesgueScalarMeasure RealMetricBackground SummableRealFunctionUP FunctionLatticeUP CompactSupportFunctionUP
  CurrentHomotopyTimePartialIntegral RadonCompactScalarIntegral RadonPositiveCompactUniqueness CurrentHomotopyIntegralMeasureUP
  CurrentHomotopyWeightedVariation CurrentHomotopyWeightedFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentHomotopyIntegralMeasure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation VT := (current_domain R nu V).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R VT)).
Local Notation Integrand phi := (@current_homotopy_slice_measure_integrand R h2 n nu j A U V f g h hHomotopy T hT phi).
Local Notation TimeIntegrand phi := (@current_homotopy_scalar_time_integrand R A (Integrand phi)).
Local Notation TimeIntegral phi b := (is_measure_subset_integral (@lebesgue_scalar_measure R)
  (`[0,1]:set (real_line_metric R)) (TimeIntegrand phi) b).

Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T.

(** Source for [current_homotopy_integral_measure_exists]: the
    actual weighted product image has every independently
    specified original slice-integral law, establishing
    existence for Federer 4.1.9, p. 363.
    The image construction is used only for this proof. *)
Theorem current_homotopy_integral_measure_exists:exists mu,
  @is_current_homotopy_integral_measure R h2 n nu j A U V f g h hHomotopy T hT mu.
Proof.
exists (@current_homotopy_weighted_image R h2 n nu j A U V f g h hHomotopy T hT).
constructor.
- exact:(@current_homotopy_weighted_image_is_measure R h2 n nu j A U V f g h hHomotopy T hT).
- exact:(@current_homotopy_weighted_image_radon R h2 n nu j A U V f g h hHomotopy T hT hProper).
- move=>phi hPhi;exact:(@current_homotopy_slice_measure_integral_exists R h2 n nu j A U V f g h hHomotopy T hT hProper phi hPhi).
Qed.
End CurrentHomotopyIntegralMeasure.
