(** Federer (1969), 4.1.9, p. 363: the exact
    original product weight is measurable and nonnegative.
    Fubini supplies measurability of its original fixed-time
    weights at almost every time, without changing the
    actual partial domains or any slice measure. *)
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
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialExtendedOrderLoci PartialProductSections ParameterizedIntegral
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP MeasurableAlmostModification
  MeasureNonnegativeIntegral MeasureIntegralBounds MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopyWeightMeasurable.
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

(** Source for [current_homotopy_weight_auxiliary_agreement]:
    the exact printed partial weight agrees almost
    everywhere with the earlier measurable auxiliary image
    norm, supporting Federer 4.1.9, p. 363. *)
Theorem current_homotopy_weight_auxiliary_agreement:
  measure_almost_equal lambda Auxiliary W.
Proof.
have hOld:=@current_original_image_weight_agreement R h2 (1+n)%N nu (1+j) AU hAU P hP h.
rewrite (@current_homotopy_product_variation R h2 n j A hInterval U hU T hT hP) in hOld.
exact:(@measure_almost_equal_trans R CT (extended_real_line R) lambda hLambda
  Auxiliary oldWeight W (measure_almost_equal_sym hOld)
  (@current_homotopy_original_weight_agreement R h2 n nu j A U V f g h hHomotopy T hT)).
Qed.

(** Source for [current_homotopy_weight_measurable]: the
    actual printed weight is measurable for the original
    product variation, supporting the last paragraph of
    Federer 4.1.9, p. 363. *)
Theorem current_homotopy_weight_measurable:is_measure_measurable_function lambda W.
Proof.
have hAux:=@current_image_weight_measurable R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2
  Gamma hGamma (distribution_representation_radon baseP) xiP
  (normalised_distribution_density_unit_bound (@NormalisedCurrent.laws R h2 (1+n)%N (1+j) AU hAU P hP))
  (distribution_representation_weak_measurable baseP).
rewrite (@current_homotopy_product_variation R h2 n j A hInterval U hU T hT hP) in hAux.
exact:(@measurable_function_almost_equal R CT (extended_real_line R) lambda hLambda
  Auxiliary W hAux current_homotopy_weight_auxiliary_agreement).
Qed.

(** Source for [current_homotopy_weight_nonnegative]: the
    original partial product weight is nonnegative on
    its original conull domain, supporting the variation
    integral in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_weight_nonnegative:
  measure_almost_everywhere lambda (partial_extended_nonnegative_locus W).
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  current_homotopy_weight_auxiliary_agreement)=>z [w [hMass hWeight]].
exists w;split;first exact:hWeight.
move:hMass;rewrite real_total_integrand_graph=>hMass.
rewrite -hMass lee_fin;exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 nu (1+j)).1 _.
Qed.

(** Source for [current_homotopy_slice_weight_measurable_almost]:
    the actual fixed-time weights are measurable at
    almost every original time, supporting the slice
    integral in Federer 4.1.9, p. 363. This
    proof uses the preceding original partial Fubini law;
    it does not redefine any exceptional slice. *)
Theorem current_homotopy_slice_weight_measurable_almost:
  measure_almost_everywhere alpha [set a:TT|is_measure_measurable_function beta (SliceWeight a)].
Proof.
have hIntegral:=(@nonnegative_measurable_function_integral R CT lambda hLambda W
  current_homotopy_weight_measurable current_homotopy_weight_nonnegative).1.
have hOuter:=@current_cartesian_radon_vertical_fubini R 1%N n AT U hAT hU alpha beta hAlpha hBeta
  hAlphaRadon hBetaRadon W _ hIntegral.
have hDomain:=measurable_function_domain hOuter.1.
apply:(@measure_almost_everywhere_mono R TT alpha hAlpha _ _ _ hDomain)=>a [b hb].
have hSection:=(parameterized_integral_specification beta
  (partial_product_vertical_section (partial_function_precompose J W)) a b).1 hb.
change (is_measure_integral beta (SliceWeight a) b) in hSection.
exact:hSection.1.
Qed.
End CurrentHomotopyWeightMeasurable.
