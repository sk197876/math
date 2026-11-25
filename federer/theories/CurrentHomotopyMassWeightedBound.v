(** Federer (1969), 4.1.9, pp. 363–364: integrate
    the sharp original variation bound over the whole
    target domain. The actual current mass is its
    total original Radon variation, including infinity.
    The partial orientation weight is not replaced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentMapDifferential
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianProductSealed
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon CurrentHomotopyProductOrientation CurrentHomotopyOriginalImage
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity CurrentHomotopyTimeVelocity CurrentHomotopyCylinder
  CurrentHomotopyProductSupport CurrentDeformationChainSealed CurrentDeformationChainPushforward
  CurrentProperSupportDomain CurrentPushforwardSealed CurrentPushforwardVariation CurrentPushforwardOrientationWeight
  CurrentHomotopyWeightedVariation CurrentHomotopyWeightMeasurable CurrentMassRepresentation CurrentMassSealed
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureNonnegativeIntegral PartialZeroExtension PartialZeroExtensionLaws
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition PartialFunctionPrecomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensity MeasureDensityTransfer MeasurePushforward RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyMassWeightedBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation S := (@current_homotopy_time_segment R A hInterval h2).
Local Notation hS := (@current_homotopy_time_representable R h2 A hInterval).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation CT := (current_domain R (1+n)%N AU).
Local Notation D := (@CartesianCurrentDomain.split R 1%N n AT U).
Local Notation time z := (@euclidean_one_project R (set_val (D z).1)).
Local Notation space z := (set_val (D z).2).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N AT hAT S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j U hU T hT).
Local Notation hNS := (@NormalisedCurrent.laws R h2 1%N 1%N AT hAT S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j U hU T hT).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNS)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation lambda := (@CartesianCurrentMeasure.value R 1%N n AT U alpha beta hAlpha hBeta).
Local Notation hLambda := (@current_cartesian_measure_is_measure R 1%N n AT U alpha beta hAlpha hBeta).
Local Notation P := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU S T).
Local Notation OT := (@CurrentOrientation.value R h2 n j U hU T hT).
Local Notation velocity := (exterior_first_inclusion (R_n R 1%N)
  (@euclidean_one_embed R 1-@euclidean_one_embed R 0)).
Local Notation DH z := (@current_map_differential R (1+n)%N nu AU h (set_val z)).
Local Notation DS z := (@current_map_differential R n nu U (@current_homotopy_slice_map R n nu h (time z)) (space z)).
Local Notation Velocity z := (@current_homotopy_time_velocity R n nu A U h (time z) (space z)).


Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation VT := (current_domain R nu V).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation hP := (@current_homotopy_original_product_representable R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation Gamma := (@NormalisedCurrent.measure R h2 (1+n)%N (1+j) AU hAU P hP).
Local Notation OP := (@CurrentOrientation.value R h2 (1+n)%N (1+j) AU hAU P hP).
Local Notation oldWeight := (@current_original_image_weight R h2 (1+n)%N nu (1+j) AU hAU P hP h).
Local Notation hDomain := (@current_map_on_domain R (1+n)%N nu AU V h image).
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Local Notation hp := (@current_homotopy_product_proper R h2 n nu j A U V f g h geometry T hProper).
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu j A U V f g h hHomotopy T hProper).


Local Notation W := (@current_homotopy_original_weight R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation Nu := (@current_homotopy_weighted_image R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation WeightIntegral := (measure_lower_integral lambda W).

(** Source for [current_homotopy_original_weight_integral]:
    the actual printed partial weight has its
    nonnegative integral for the original product variation,
    supporting Federer 4.1.9, pp. 363–364, by 2.4.4(2).
    Positive infinity is retained as an integral value. *)
Theorem current_homotopy_original_weight_integral:is_measure_integral lambda W WeightIntegral.
Proof.
exact:(@nonnegative_measurable_function_integral R CT lambda hLambda W
  (@current_homotopy_weight_measurable R h2 n nu j A U V f g h hHomotopy T hT)
  (@current_homotopy_weight_nonnegative R h2 n nu j A U V f g h hHomotopy T hT)).1.
Qed.

(** Source for [current_homotopy_weighted_image_total]: the
    total original weighted image is the integral of
    the exact original weight, supporting the affine
    mass estimate in Federer 4.1.9, p. 364,
    by the density definition of 2.4.10, p. 85. *)
Theorem current_homotopy_weighted_image_total:Nu setT=WeightIntegral.
Proof.
have hWhole:is_measure_integral lambda
    (partial_function_zero_extension (0:extended_real_line R) setT W) WeightIntegral.
  apply:(@measure_integral_graph_equivalent R CT lambda _ _ _ _ current_homotopy_original_weight_integral)=>z w.
  exact:iff_sym (partial_zero_extension_whole_graph (0:extended_real_line R) W z w).
have hUpper:=@measure_upper_integral_unique R CT lambda _ _ WeightIntegral
  (measure_upper_integral_specification lambda _) hWhole.2.1.
change (measure_with_density lambda W (hDomain @^-1` setT)=WeightIntegral).
have hSet:hDomain @^-1` setT=setT by apply/seteqP;split=>z;by [].
rewrite hSet (measure_with_density_laws lambda W setT).
exact:hUpper.
Qed.

(** Source for [current_homotopy_mass_weight_bound]: the
    actual deformation-chain mass is at most the
    original printed velocity/spatial weight integral,
    supporting the first affine estimate in Federer
    4.1.9, p. 364. No finite total mass is imposed. *)
Theorem current_homotopy_mass_weight_bound:
  (@CurrentMass.value R h2 nu (1+j) V hV chain<=WeightIntegral)%E.
Proof.
pose hChain:=@current_deformation_chain_representable R h2 n nu j A U V f g h hHomotopy T hT hProper.
rewrite (@current_represented_mass_total R h2 nu (1+j) V hV chain hChain).
apply:(le_trans (@current_homotopy_sharp_weighted_variation R h2 n nu j A U V f g h hHomotopy
  T hT hProper hChain setT)).
rewrite current_homotopy_weighted_image_total;exact:lexx.
Qed.
End CurrentHomotopyMassWeightedBound.
