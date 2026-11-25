(** Federer (1969), 4.1.9, p. 364: compare the
    actual original partial orientation weight with the
    printed affine scalar integrand. The proof uses
    the original conull time band, original orientation
    and already proved all-degree mass estimate. *)
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
  EuclideanHomOperator OperatorNormUP OperatorNormSealed FiniteCoordinates CurrentOrientationAlmost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentAffineHomotopyWeightBound.
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

(** Source for [current_homotopy_product_closed_band_conull]:
    the original time-product variation is concentrated
    on the original closed cylinder in the time
    coordinate, supporting Federer 4.1.9, pp. 363–364.
    No restriction of the original source current is added. *)
Lemma current_homotopy_product_closed_band_conull:
  measure_almost_everywhere lambda [set z:CT|0<=time z<=1].
Proof.
have hTime:=@product_almost_everywhere_first_factor R TT XT alpha beta hAlpha hBeta _
  (@current_homotopy_time_band_conull R h2 A hInterval).
apply:(@measure_bijection_almost_everywhere_iff R PT CT mu lambda J D hBij _).1.
apply:(@measure_almost_everywhere_mono R PT mu hm _ _ _ hTime)=>z hz.
change (0<=@euclidean_one_project R (set_val (D (J z)).1)<=1).
by rewrite current_cartesian_domain_join_split.
Qed.

Hypothesis hAffine:forall t x,A t->U x->
  @current_homotopy_slice_map R n nu h t x=(1-t)*:f x+t*:g x.
Arguments hAffine : clear implicits.

(** Source for [current_affine_original_weight_bound]: the
    original partial norm weight is at most
    |g-f|[(1-t)||Df||+t||Dg||]^j almost everywhere
    for the original product variation, supporting
    Federer 4.1.9, p. 364. Simplicity of T,
    finite mass and whole-domain properness are not required. *)
Theorem current_affine_original_weight_bound:
  measure_almost_everywhere lambda
    (partial_extended_le_locus W (real_total_integrand (fun z:CT=>E (D z)))).
Proof.
have hFactors:=@current_cartesian_original_factor_agreement R h2 1%N n 1%N j AT U hAT hU S T hS hT.
have hGood:=@measure_almost_everywhere_and R CT lambda hLambda _ _
  current_homotopy_product_closed_band_conull hFactors.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _ hGood)=>z [ht [_ hEta]].
pose w:=(MassValue z (Teta (D z).2))%:E.
exists w,(E (D z))%:E;split.
- have hGraph:partial_function_graph (SliceWeight (D z).1) (D z).2 w.
    apply:(@current_homotopy_slice_weight_graph R h2 n nu j A U V f g h hHomotopy T hT
      (D z).1 (D z).2 w).2.
    exists (Teta (D z).2);by split.
  change (partial_function_graph W (J ((D z).1,(D z).2)) w) in hGraph.
  by rewrite -surjective_pairing current_cartesian_domain_split_join in hGraph.
split;first by rewrite real_total_integrand_graph.
have hEnvelope:=@homotopy_affine_power_envelope_value R n j A U a b c (D z).1 (D z).2 ht.
rewrite -(surjective_pairing (D z)) in hEnvelope.
rewrite /w lee_fin hEnvelope.
exact:(@current_affine_homotopy_mass_integrand_bound R h2 n nu j A U V f g h hHomotopy hAffine
  (time z) (space z) (Teta (D z).2) ht (set_valP (D z).2)
  (normalised_distribution_density_unit_bound hNT (D z).2)).
Qed.
End CurrentAffineHomotopyWeightBound.
