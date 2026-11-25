(** Federer (1969), 4.1.9, p. 364: all three
    original affine deformation-chain mass estimates. The
    exact time integral equals the printed mixed-power
    average and is at most the endpoint-power maximum.
    Infinite masses, zero endpoints and degree zero remain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentMapDifferential
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon CurrentCartesianProductSealed
  CurrentHomotopyProductOrientation CurrentHomotopyOriginalImage CurrentHomotopyWeightedVariation CurrentHomotopySliceMeasures
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity CurrentHomotopyTimeVelocity
  CurrentImageDensityPairing CurrentImageWeightRadon CurrentPushforwardOrientationWeight
  CurrentCartesianRadonFubini DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci PartialProductSections ParameterizedIntegral
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP MeasurableAlmostModification
  MeasureNonnegativeIntegral MeasureIntegralBounds MeasureIntegralUP SummableRealFunctionUP
  CurrentHomotopyTimeScalarIntegral CurrentAffineHomotopyMassIntegrand CurrentAffineHomotopyScalarFields
  CurrentCartesianOriginalDensity CartesianMeasureAlmost ProductMeasure HomotopyAffinePowerFields
  EuclideanHomOperator OperatorNormUP OperatorNormSealed FiniteCoordinates CurrentOrientationAlmost
  CurrentAffineHomotopyWeightBound CurrentHomotopyMassWeightedBound HomotopyAffinePowerFubini
  CurrentMassSealed CurrentDeformationChainSealed CurrentHomotopyCylinder
  MeasureBijectionIntegralTransport MeasureIntegralGraphEquivalence MeasureIntegralComparison
  MeasureIntegralBounds MeasureSubsetIntegral RealMetricBackground LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentAffineHomotopyMass.
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
Local Notation hP := (@current_homotopy_original_product_representable R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation Gamma := (@NormalisedCurrent.measure R h2 (1+n)%N (1+j) AU hAU P hP).
Local Notation xiP := (@NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j) AU hAU P hP).
Local Notation baseP := (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 (1+n)%N (1+j) AU hAU P hP)).
Local Notation hGamma := (distribution_representation_measure baseP).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation W := (@current_homotopy_original_weight R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation oldWeight := (@current_original_image_weight R h2 (1+n)%N nu (1+j) AU hAU P hP h).
Local Notation Auxiliary := (real_total_integrand (fun z=>@current_vector_mass R h2 nu (1+j)
  (@current_image_density R (1+n)%N nu (1+j) AU h xiP z))).
Local Notation TT := (current_domain R 1%N AT).
Local Notation XT := (current_domain R n U).
Local Notation J := (@CartesianCurrentDomain.join R 1%N n AT U).
Local Notation hAlphaRadon := (distribution_representation_radon (normalised_distribution_representation_laws hNS)).
Local Notation hBetaRadon := (distribution_representation_radon (normalised_distribution_representation_laws hNT)).
Local Notation SliceWeight := (@current_homotopy_slice_weight R h2 n nu j A U V f g h hHomotopy T hT).


Local Notation PT := (Choice.clone (TT*XT)%type _).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation hBij := (@current_cartesian_measure_bijection R 1%N n AT U alpha beta hAlpha hBeta).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation Teta := (@NormalisedCurrent.auxiliary_density R h2 n j U hU T hT).
Local Notation a := (fun x:XT=>NY (g (set_val x)-f (set_val x))).
Local Notation b := (fun x:XT=>Op (@current_map_differential R n nu U f (set_val x))).
Local Notation c := (fun x:XT=>Op (@current_map_differential R n nu U g (set_val x))).
Local Notation E := (@homotopy_affine_power_envelope R n j A U a b c).
Local Notation MassValue z xi := (@current_vector_mass R h2 nu (1+j)
  (exterior_product (exterior_first_inclusion Y (Velocity z))
    (exterior_power_map (hom_as_linear (DS z)) j xi))).


Local Notation Mean := (@homotopy_affine_power_mean R n j U a b c).
Local Notation Max := (@homotopy_affine_power_maximum R n j U a b c).
Local Notation Joint := (real_total_integrand E).
Local Notation Value := (measure_lower_integral mu Joint).
Local Notation MaxValue := (measure_lower_integral beta (real_total_integrand Max)).
Local Notation Spatial t := (real_total_integrand (fun x:XT=>a x*((1-t)*b x+t*c x)^+j)).
Local Notation Outer := (parameterized_integral beta (fun t=>Spatial t)).
Local Notation TargetEnvelope := (real_total_integrand (fun z:CT=>E (D z))).
Hypothesis hAffine:forall t x,A t->U x->
  @current_homotopy_slice_map R n nu h t x=(1-t)*:f x+t*:g x.
Arguments hAffine : clear implicits.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu j A U V f g h hHomotopy T hProper).
Local Notation M := (@CurrentMass.value R h2 nu (1+j) V hV chain).
Local Notation ha := (fun x:XT=>inner_norm_nonnegative (@euclidean_inner_productP R nu) (g (set_val x)-f (set_val x))).
Local Notation hb := (fun x:XT=>real_seminorm_nonnegative (@euclidean_operator_norm_is_norm R n nu).1
  (@current_map_differential R n nu U f (set_val x))).
Local Notation hc := (fun x:XT=>real_seminorm_nonnegative (@euclidean_operator_norm_is_norm R n nu).1
  (@current_map_differential R n nu U g (set_val x))).
Local Notation hAContinuous := (@current_affine_displacement_norm_continuous R n nu A U V f g h hHomotopy).
Local Notation hBContinuous := (@current_affine_endpoint_differential_norms_continuous R n nu A U V f g h hHomotopy).1.
Local Notation hCContinuous := (@current_affine_endpoint_differential_norms_continuous R n nu A U V f g h hHomotopy).2.

(** Source for [current_affine_product_envelope_integral]:
    the original affine scalar envelope has its actual
    product-variation integral, supporting the first mass
    bound in Federer 4.1.9, p. 364. The value
    is allowed to be infinite. *)
Lemma current_affine_product_envelope_integral:is_measure_integral mu Joint Value.
Proof.
exact:(@homotopy_affine_joint_integral R h2 n j A hInterval U hU a b c ha hb hc
  hAContinuous hBContinuous hCContinuous beta hBeta hBetaRadon).
Qed.

(** Source for [current_affine_original_envelope_integral]:
    the original product-coordinate identification preserves
    the affine envelope integral on the original A times U,
    supporting Federer 4.1.9, p. 364. No private
    representation of the coordinate maps is unfolded. *)
Lemma current_affine_original_envelope_integral:is_measure_integral lambda TargetEnvelope Value.
Proof.
apply:(@measure_bijection_integral_iff R PT CT mu lambda hm J D hBij TargetEnvelope Value).1.
apply:(@measure_integral_graph_equivalent R PT mu Joint _ Value _ current_affine_product_envelope_integral)=>z w.
change (partial_function_graph (real_total_integrand E) z w<->
  partial_function_graph (real_total_integrand (fun z:CT=>E (D z))) (J z) w).
by rewrite !real_total_integrand_graph current_cartesian_domain_join_split.
Qed.

(** Source for [current_affine_homotopy_mass_bound]: the
    actual affine deformation-chain mass is at most
    the original time/spatial integral, supporting the
    first displayed inequality in Federer 4.1.9, p. 364.
    Only original support-cylinder properness is imposed. *)
Theorem current_affine_homotopy_mass_bound:(M<=Value)%E.
Proof.
apply:(le_trans (@current_homotopy_mass_weight_bound R h2 n nu j A U V f g h hHomotopy T hT hProper)).
exact:(@measure_integral_monotone R CT lambda hLambda W TargetEnvelope _ Value
  (@current_homotopy_original_weight_integral R h2 n nu j A U V f g h hHomotopy T hT)
  current_affine_original_envelope_integral
  (@current_affine_original_weight_bound R h2 n nu j A U V f g h hHomotopy T hT hAffine)).
Qed.

(** Source for [current_affine_homotopy_mass_estimates]: the
    complete original three-line estimate in Federer
    4.1.9, p. 364: the actual chain mass is
    bounded by the literal time integral, that integral
    equals the spatial mixed-power mean integral, and
    the mean is bounded by the endpoint-power maximum
    integral. All integral values are actual values;
    no extra integrability or finite-mass premise is used. *)
Theorem current_affine_homotopy_mass_estimates:
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R)) Outer Value /\
  is_measure_integral beta (real_total_integrand Mean) Value /\
  is_measure_integral beta (real_total_integrand Max) MaxValue /\
  (M<=Value /\Value<=MaxValue)%E.
Proof.
split.
- exact:(@homotopy_affine_literal_time_integral R h2 n j A hInterval U hU a b c ha hb hc
    hAContinuous hBContinuous hCContinuous beta hBeta hBetaRadon).
split.
- exact:(@homotopy_affine_mean_integral R h2 n j A hInterval U hU a b c ha hb hc
    hAContinuous hBContinuous hCContinuous beta hBeta hBetaRadon).
split.
- exact:(@homotopy_affine_maximum_integral R n j U a b c ha hb hc
    hAContinuous hBContinuous hCContinuous beta hBeta hBetaRadon).
split;first exact:current_affine_homotopy_mass_bound.
exact:(@homotopy_affine_mean_integral_maximum_bound R h2 n j A hInterval U hU a b c ha hb hc
  hAContinuous hBContinuous hCContinuous beta hBeta hBetaRadon).
Qed.
End CurrentAffineHomotopyMass.
