(** Federer (1969), 4.1.9, p. 363: the exact
    weighted Radon image has the printed slice integral
    on every original positive compact scalar test.
    The original Fubini theorem preserves the partial
    inner integral and the literal scalar time interval. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentMapDifferential
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianProductSealed
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon CurrentHomotopyProductOrientation CurrentHomotopyOriginalImage CurrentHomotopyOriginalFubini
  CurrentHomotopyTimePartialIntegral CurrentHomotopyWeightedVariation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity CurrentHomotopyTimeVelocity CurrentHomotopyCylinder
  CurrentHomotopyProductSupport CurrentDeformationChainSealed CurrentDeformationChainPushforward
  CurrentProperSupportDomain CurrentPushforwardSealed CurrentPushforwardVariation CurrentPushforwardOrientationWeight CurrentPushforwardWeight CurrentImageDensityPairing
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition PartialFunctionPrecomposition PartialFunctionSourcePostcomposition PartialProductSections ParameterizedIntegral
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralAlmostEquality MeasureSubsetIntegral RadonCompactScalarIntegral RealIntegralFunctionalUP
  FunctionLatticeUP CompactSupportFunctionUP SummableRealFunctionUP RealMetricBackground LebesgueScalarMeasure MeasureDensity MeasureDensityTransfer MeasurePushforward RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopyWeightedFubini.
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
Local Notation xiP := (@NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j) AU hAU P hP).
Local Notation ImageP := (@current_image_density R (1+n)%N nu (1+j) AU h xiP).
Local Notation AuxiliaryWeight := (real_total_integrand (fun z=>@current_vector_mass R h2 nu (1+j) (ImageP z))).
Local Notation oldNu := (@current_pushforward_weight R h2 (1+n)%N nu (1+j) AU V hAU h image P hP).
Local Notation oldHm := (@current_pushforward_weight_measure R h2 (1+n)%N nu (1+j) AU V hAU h image P hP).
Local Notation oldHr := (@current_pushforward_weight_radon R h2 (1+n)%N nu (1+j) AU V hAU hV
  h image hHomotopy.2 P hP hp).
Local Notation J := (@CartesianCurrentDomain.join R 1%N n AT U).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R VT)).

(** Source for [current_homotopy_weighted_image_auxiliary]:
    the exact printed weighted image is the previously
    proved Radon image with its auxiliary normalized
    density, supporting Federer 4.1.9, p. 363.
    This equality is on every set; it does not replace
    the original partial weight in the public formula. *)
Theorem current_homotopy_weighted_image_auxiliary:Nu=oldNu.
Proof.
rewrite /current_homotopy_weighted_image
  -(@current_homotopy_original_density_measure R h2 n nu j A U V f g h hHomotopy T hT)
  (@current_original_image_density_measure R h2 (1+n)%N nu (1+j) AU hAU P hP h).
by [].
Qed.

(** Source for [current_homotopy_weighted_image_is_measure]:
    the exact original weighted image is a measure,
    supporting Federer 4.1.9, p. 363. Infinite
    total mass is retained. *)
Theorem current_homotopy_weighted_image_is_measure:is_measure Nu.
Proof. rewrite current_homotopy_weighted_image_auxiliary;exact:oldHm. Qed.

(** Source for [current_homotopy_weighted_scalar_test]: the
    literal original integrand phi(h(t,x)) times the printed
    partial velocity/spatial mass weight, supporting the
    integral of image measures in Federer 4.1.9, p. 363.
    Its domain is exactly the original weight domain. *)
Definition current_homotopy_weighted_scalar_test (phi:VT->R):partial_function CT (extended_real_line R):=
  partial_function_source_postcompose W (fun z w=>((phi (hDomain z))%:E*w)%E).

(** Source for [current_homotopy_weighted_compact_integral]:
    each positive compact target test has its exact original
    weighted product integral, supporting the last inequality
    in Federer 4.1.9, p. 363, by 2.4.10 and
    2.4.18. Only the printed cylinder properness is used. *)
Theorem current_homotopy_weighted_compact_integral phi (hG:Kplus phi) a:
  is_measure_integral Nu (real_total_integrand phi) a->
  is_measure_integral lambda (current_homotopy_weighted_scalar_test phi) a.
Proof.
move=>hTarget.
have hOriginal:=@current_pushforward_weight_compact_integral R h2 (1+n)%N nu (1+j)
  AU V hAU hV h image hHomotopy.2 P hP hp phi hG.
have hOldTarget:=@radon_positive_compact_integral_laws R VT oldNu oldHm oldHr phi hG.
have hOldInput:is_measure_integral oldNu (real_total_integrand phi) a.
  rewrite -current_homotopy_weighted_image_auxiliary;exact:hTarget.
have hValue:=measure_integral_unique hOldTarget hOldInput.
rewrite hValue (@current_homotopy_product_variation R h2 n j A hInterval U hU T hT hP) in hOriginal.
have hOld:=@current_original_image_weight_agreement R h2 (1+n)%N nu (1+j) AU hAU P hP h.
rewrite (@current_homotopy_product_variation R h2 n j A hInterval U hU T hT hP) in hOld.
have hAgreement:=@measure_almost_equal_trans R CT (extended_real_line R) lambda hLambda
  AuxiliaryWeight oldWeight W (measure_almost_equal_sym hOld)
  (@current_homotopy_original_weight_agreement R h2 n nu j A U V f g h hHomotopy T hT).
apply:(@measure_integral_almost_equal R CT lambda hLambda _ _ a hOriginal).
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _ hAgreement)
  =>z [w [hMass hWeight]].
exists ((phi (hDomain z))%:E*w)%E;split.
- move:hMass;rewrite real_total_integrand_graph=>hMass.
  by rewrite real_total_integrand_graph EFinM hMass.
- exists w;by split.
Qed.

(** Source for [current_homotopy_weighted_compact_fubini]:
    the exact weighted image measure has the original
    time integral of its spatial slice integrals on every
    positive compact target test, Federer 4.1.9, p. 363.
    Inner integrals retain their actual partial domains. *)
Theorem current_homotopy_weighted_compact_fubini phi (hG:Kplus phi) a:
  is_measure_integral Nu (real_total_integrand phi) a->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
    (@current_homotopy_scalar_time_integrand R A
      (parameterized_integral beta (partial_product_vertical_section
        (partial_function_precompose J (current_homotopy_weighted_scalar_test phi))))) a.
Proof.
move=>hTarget.
exact:(@current_homotopy_original_fubini R h2 n j A hInterval U hU T hT _ a
  (current_homotopy_weighted_compact_integral hG hTarget)).
Qed.

(** Source for [current_homotopy_weighted_compact_fubini_exists]:
    every original positive compact scalar test has a finite
    integral and the exact printed iterated integral,
    supporting Federer 4.1.9, p. 363. Existence is
    proved, rather than left as a conditional statement. *)
Theorem current_homotopy_weighted_compact_fubini_exists phi:Kplus phi->exists a:R,
  is_measure_integral Nu (real_total_integrand phi) a%:E /\
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
    (@current_homotopy_scalar_time_integrand R A
      (parameterized_integral beta (partial_product_vertical_section
        (partial_function_precompose J (current_homotopy_weighted_scalar_test phi))))) a%:E.
Proof.
move=>hG.
pose hr:=@current_homotopy_weighted_image_radon R h2 n nu j A U V f g h hHomotopy T hT hProper.
pose hm:=current_homotopy_weighted_image_is_measure.
pose a:=@radon_positive_compact_integral R VT Nu hm hr phi.
have hIntegral:=@radon_positive_compact_integral_laws R VT Nu hm hr phi hG.
exists a;split;first exact:hIntegral.
exact:(@current_homotopy_weighted_compact_fubini phi hG a%:E hIntegral).
Qed.
End CurrentHomotopyWeightedFubini.
