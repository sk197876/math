(** Federer (1969), 4.1.9, p. 363: the exact
    represented homotopy variation bound before the Fubini
    identification of its slice integral. Preserve the
    actual original partial density, all target sets and
    the printed properness on the closed time cylinder. *)
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
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition PartialFunctionPrecomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensity MeasureDensityTransfer MeasurePushforward RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopyWeightedVariation.
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

(** Source for [current_homotopy_original_weight]: the
    literal partial weight ||h-dot_t wedge Lambda_j Dh_t(vec T)||,
    supporting the final displayed inequality in Federer
    4.1.9, p. 363. Its domain is exactly the
    original partial orientation domain of T pulled back
    to the original time-space product. *)
Definition current_homotopy_original_weight:partial_function CT (extended_real_line R):=
  partial_function_postcompose
    (partial_function_pair (partial_function_total (fun z:CT=>z))
      (partial_function_precompose (fun z:CT=>(D z).2) OT))
    (fun za:CT*exterior_power X j=>
      (@current_vector_mass R h2 nu (1+j)
        (exterior_product (exterior_first_inclusion Y (Velocity za.1))
          (exterior_power_map (hom_as_linear (DS za.1)) j za.2)))%:E).

(** Source for [current_homotopy_original_weight_agreement]:
    the original exterior-image weight of the actual time
    product equals the printed velocity/spatial weight
    almost everywhere for the original product variations,
    supporting Federer 4.1.9, p. 363. *)
Theorem current_homotopy_original_weight_agreement:
  measure_almost_equal lambda oldWeight current_homotopy_original_weight.
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (@current_homotopy_original_exterior_image R h2 n nu j A U V f g h hHomotopy T hT hP))
  =>z [eta [theta [hEta [hTheta hEqual]]]].
pose w:=(@current_vector_mass R h2 nu (1+j)
  (exterior_product (exterior_first_inclusion Y (Velocity z))
    (exterior_power_map (hom_as_linear (DS z)) j eta)))%:E.
exists w;split.
- exists (z,theta);split;first by split.
  by rewrite hEqual.
- exists (z,eta);split;first by split.
  by [].
Qed.

(** Source for [current_homotopy_original_density_measure]:
    the actual weighted product measure equals the one
    with the exact printed partial density on every set,
    supporting Federer 4.1.9, p. 363, by 2.4.10. *)
Theorem current_homotopy_original_density_measure:
  measure_with_density Gamma oldWeight=
    measure_with_density lambda current_homotopy_original_weight.
Proof.
rewrite (@current_homotopy_product_variation R h2 n j A hInterval U hU T hT hP).
have hDensity:=@measure_density_almost_equal R CT lambda
  (measure_with_density lambda oldWeight) hLambda oldWeight current_homotopy_original_weight
  (measure_with_density_laws lambda oldWeight) current_homotopy_original_weight_agreement.
apply:funext=>B;exact:(eq_trans (hDensity B)
  (esym (measure_with_density_laws lambda current_homotopy_original_weight B))).
Qed.

(** Source for [current_homotopy_weighted_image]: the
    exact image of the original weighted time product,
    supporting the integral of slice image measures in
    Federer 4.1.9, p. 363. The density retains
    the actual original partial orientation. *)
Definition current_homotopy_weighted_image:set VT->\bar R:=
  measure_pushforward hDomain (measure_with_density lambda current_homotopy_original_weight).

(** Source for [current_homotopy_weighted_image_radon]: the
    exact weighted image is Radon under the printed
    closed-cylinder properness, supporting Federer 4.1.9,
    p. 363. No global properness or finite mass is added. *)
Theorem current_homotopy_weighted_image_radon:is_radon_measure current_homotopy_weighted_image.
Proof.
rewrite /current_homotopy_weighted_image -current_homotopy_original_density_measure.
exact:(@current_original_pushforward_weight_radon R h2 (1+n)%N nu (1+j)
  AU V hAU hV P hP h image hHomotopy.2 hp).
Qed.

(** Source for [current_deformation_chain_representable]:
    the original deformation chain of a represented current
    is representable, supporting the variation inequality
    in Federer 4.1.9, p. 363, by 4.1.7, p. 359. *)
Theorem current_deformation_chain_representable:
  @is_integration_representable_current R h2 nu (1+j) V hV chain.
Proof.
rewrite (@current_deformation_chain_pushforward R h2 n nu j A U V f g h hHomotopy T hProper).
exact:(@current_pushforward_representable R h2 (1+n)%N nu (1+j)
  AU V hAU hV P hP h image hHomotopy.2 hp).
Qed.

(** Source for [current_homotopy_sharp_weighted_variation]:
    the actual deformation-chain variation is at most
    the exact original weighted image on every target set,
    supporting the sharp final inequality in Federer
    4.1.9, p. 363. The subsequent Fubini adapter
    identifies this Radon measure with its slice integral. *)
Theorem current_homotopy_sharp_weighted_variation
    (hChain:@is_integration_representable_current R h2 nu (1+j) V hV chain):forall B,
  (@NormalisedCurrent.measure R h2 nu (1+j) V hV chain hChain B<=
    current_homotopy_weighted_image B)%E.
Proof.
rewrite /current_homotopy_weighted_image -current_homotopy_original_density_measure.
have hEqual:=@current_deformation_chain_pushforward R h2 n nu j A U V f g h hHomotopy T hProper.
rewrite hEqual in hChain *.
exact:(@current_pushforward_original_weighted_variation R h2 (1+n)%N nu (1+j)
  AU V hAU hV P hP h image hHomotopy.2 hp hChain).
Qed.
End CurrentHomotopyWeightedVariation.
