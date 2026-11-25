(** Federer (1969), 4.1.9, p. 363: identify the
    sharp Radon bound with the original integral of
    actual weighted slice image measures. The two
    preceding integral laws supply the exact partial
    inner integrals and the literal interval [0,1]. *)
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
  MeasureNonnegativeIntegral MeasureIntegralBounds MeasureIntegralUP SummableRealFunctionUP
  CurrentHomotopyWeightMeasurable CurrentHomotopySliceIntegral CurrentHomotopyWeightedFubini
  CurrentHomotopyTimePartialIntegral CurrentProperSupportDomain CurrentHomotopyCylinder
  PartialFunctionSourcePostcomposition PartialDensityProduct MeasureIntegralGraphEquivalence
  ParameterizedMeasureIntegral ParameterizedMeasureIntegralUP MeasureIntegralAlmostEquality
  FunctionLatticeUP CompactSupportFunctionUP MeasureSubsetIntegral LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopySliceMeasureIntegral.
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


Local Notation VT := (current_domain R nu V).
Local Notation hDomain := (@current_map_on_domain R (1+n)%N nu AU V h image).
Local Notation SliceMap := (@current_homotopy_slice_domain_map R n nu A U V f g h hHomotopy).
Local Notation SliceMeasure := (@current_homotopy_slice_weighted_measure R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation WeightedTest phi := (@current_homotopy_weighted_scalar_test R h2 n nu j A U V f g h hHomotopy T hT phi).
Local Notation SectionTest phi := (partial_product_vertical_section (partial_function_precompose J (WeightedTest phi))).
Local Notation Nu := (@current_homotopy_weighted_image R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R VT)).

(** Source for [current_homotopy_slice_test_graph]: the
    original product integrand at fixed time is precisely
    the original slice density product, supporting the
    image-measure integral in Federer 4.1.9, p. 363.
    The partial orientation domain is preserved exactly. *)
Lemma current_homotopy_slice_test_graph (phi:VT->R) (a:TT) (x:XT) z:
  partial_function_graph (SectionTest phi a) x z<->
  partial_function_graph
    (partial_density_product (real_total_integrand (fun x=>phi (SliceMap a x))) (SliceWeight a)) x z.
Proof.
change ((exists w,partial_function_graph W (J (a,x)) w /\
  ((phi (hDomain (J (a,x))))%:E*w)%E=z)<->
  partial_function_graph
    (partial_density_product (real_total_integrand (fun x=>phi (SliceMap a x))) (SliceWeight a)) x z).
rewrite partial_density_product_graph.
split.
- move=>[w [hw hValue]].
  exists (phi (SliceMap a x))%:E,w;split;first by rewrite real_total_integrand_graph.
  split;first exact:hw.
  by rewrite (@current_homotopy_slice_domain_value R n nu A U V f g h hHomotopy a x) in hValue.
- move=>[u [w [hPhi [hw hValue]]]].
  move:hPhi;rewrite real_total_integrand_graph=>hPhi;subst u.
  exists w;split;first exact:hw.
  by rewrite (@current_homotopy_slice_domain_value R n nu A U V f g h hHomotopy a x).
Qed.

(** Source for [current_homotopy_slice_test_integral_iff]:
    at every measurable original slice, its spatial
    section integral is exactly the integral for the
    actual weighted image measure, supporting Federer
    4.1.9, p. 363, by 2.4.10 and 2.4.18. *)
Theorem current_homotopy_slice_test_integral_iff (phi:VT->R) (a:TT):
  continuous (phi:VT->real_line_metric R)->
  is_measure_measurable_function beta (SliceWeight a)->forall b,
  is_measure_integral beta (SectionTest phi a) b<->
  is_measure_integral (SliceMeasure a) (real_total_integrand phi) b.
Proof.
move=>hPhi hWeight b.
have hDensity:=@current_homotopy_slice_density_integral_iff R h2 n nu j A U V f g h hHomotopy T hT a phi hPhi hWeight b.
split=>hIntegral.
- apply:hDensity.2;exact:(measure_integral_graph_equivalent
    (current_homotopy_slice_test_graph phi a) hIntegral).
- apply:(@measure_integral_graph_equivalent R XT beta _ _ b _ (hDensity.1 hIntegral))=>x z.
  exact:iff_sym (current_homotopy_slice_test_graph phi a x z).
Qed.

(** Source for [current_homotopy_slice_measure_integrand]: the
    original time function integrates phi against each
    actual weighted slice image, supporting the measure
    integral in Federer 4.1.9, p. 363. Its
    values exist exactly on the actual integral domain. *)
Definition current_homotopy_slice_measure_integrand (phi:VT->R):
    partial_function TT (extended_real_line R):=
  parameterized_measure_integral SliceMeasure (fun _=>real_total_integrand phi).

(** Source for [current_homotopy_slice_measure_integral]: the
    exact weighted Radon bound has the printed integral
    of original weighted slice images on every positive
    compact scalar test, Federer 4.1.9, p. 363.
    Only original closed-cylinder support properness is used. *)
Theorem current_homotopy_slice_measure_integral
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T)
    phi (hPhi:Kplus phi) b:
  is_measure_integral Nu (real_total_integrand phi) b->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
    (@current_homotopy_scalar_time_integrand R A (current_homotopy_slice_measure_integrand phi)) b.
Proof.
move=>hTarget.
have hProduct:=@current_homotopy_weighted_compact_integral R h2 n nu j A U V f g h hHomotopy T hT
  hProper phi hPhi b hTarget.
have hOuter:=@current_cartesian_radon_vertical_fubini R 1%N n AT U hAT hU alpha beta
  hAlpha hBeta hAlphaRadon hBetaRadon (WeightedTest phi) b hProduct.
have hGood:=@measure_almost_everywhere_and R TT alpha hAlpha _ _
  (@current_homotopy_slice_weight_measurable_almost R h2 n nu j A U V f g h hHomotopy T hT)
  (measurable_function_domain hOuter.1).
have hAgreement:measure_almost_equal alpha (parameterized_integral beta (SectionTest phi))
    (current_homotopy_slice_measure_integrand phi).
  apply:(@measure_almost_everywhere_mono R TT alpha hAlpha _ _ _ hGood).
  move=>a [hWeight [c hc]];exists c;split;first exact:hc.
  apply:(parameterized_measure_integral_specification SliceMeasure (fun _=>real_total_integrand phi) a c).2.
  exact:(@current_homotopy_slice_test_integral_iff phi a hPhi.1.1 hWeight c).1
    ((parameterized_integral_specification beta (SectionTest phi) a c).1 hc).
have hActual:=@measure_integral_almost_equal R TT alpha hAlpha _ _ b hOuter hAgreement.
exact:(@current_homotopy_time_partial_integral_iff R h2 A hInterval _ b).1 hActual.
Qed.

(** Source for [current_homotopy_slice_measure_integral_exists]:
    the original measure integral exists with a finite
    value on each positive compact test, supporting
    the final inequality in Federer 4.1.9, p. 363.
    The conclusion concerns the actual slice measures. *)
Theorem current_homotopy_slice_measure_integral_exists
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T)
    phi:Kplus phi->exists b:R,
  is_measure_integral Nu (real_total_integrand phi) b%:E /\
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
    (@current_homotopy_scalar_time_integrand R A (current_homotopy_slice_measure_integrand phi)) b%:E.
Proof.
move=>hPhi.
have[b [hTarget _]]:=@current_homotopy_weighted_compact_fubini_exists R h2 n nu j A U V f g h hHomotopy T hT hProper phi hPhi.
exists b;split;first exact:hTarget.
exact:(@current_homotopy_slice_measure_integral hProper phi hPhi b%:E hTarget).
Qed.
End CurrentHomotopySliceMeasureIntegral.
