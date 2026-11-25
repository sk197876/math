(** Federer (1969), 4.1.9, p. 363: the original
    weighted slice image has its literal spatial integral.
    Reuse the actual change-of-density and image integral
    laws of 2.4.10 and 2.4.18. All partial
    domains and extended integral values are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap ExteriorGrading ExteriorPowers
  ExteriorMaps ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentMapDifferential CurrentIntegrationCriterion
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopyTimeVelocity CurrentHomotopyCylinder CurrentHomotopySliceProper
  CurrentHomotopyWeightedVariation CurrentProperSupport CurrentProperSupportDomain CurrentProperSupportMapAgreement
  NormalisedCurrentSealed CurrentOrientationSealed CurrentOrientationAlmost
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionPrecomposition PartialFunctionPostcomposition PartialFunctionPair
  CurrentHomotopySliceMeasures CurrentHomotopySliceClass NormClassOneUP CurrentCartesianDomain
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureDensityTransfer MeasureChangeOfDensity PartialDensityProduct
  MeasurableFunctionUP CompactSupportSummability RadonBorelRegularity BorelRegularMeasureUP
  RealMetricBackground FunctionLatticeUP CompactSupportFunctionUP SummableRealFunctionUP RadonWeightedPushforwardIntegral
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensity MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopySliceIntegral.
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
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation TT := (current_domain R 1%N AT).
Local Notation XT := (current_domain R n U).
Local Notation VT := (current_domain R nu V).
Local Notation CT := (current_domain R (1+n)%N AU).
Local Notation J := (@CartesianCurrentDomain.join R 1%N n AT U).
Local Notation D := (@CartesianCurrentDomain.split R 1%N n AT U).
Local Notation time a := (@euclidean_one_project R (set_val a)).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation beta := (@NormalisedCurrent.measure R h2 n j U hU T hT).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j U hU T hT).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j U hU T hT).
Local Notation OT := (@CurrentOrientation.value R h2 n j U hU T hT).
Local Notation W := (@current_homotopy_original_weight R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation slice a := (@current_homotopy_slice_map R n nu h (time a)).
Local Notation sliceImage a := (@current_homotopy_slice_image R n nu A U V f g h geometry (time a) (set_valP a)).
Local Notation MassValue a x xi := (@current_vector_mass R h2 nu (1+j)
  (exterior_product (exterior_first_inclusion Y
    (@current_homotopy_time_velocity R n nu A U h (time a) (set_val x)))
    (exterior_power_map (hom_as_linear
      (@current_map_differential R n nu U (slice a) (set_val x))) j xi))).


Local Notation SliceWeight := (@current_homotopy_slice_weight R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation SliceMap := (@current_homotopy_slice_domain_map R n nu A U V f g h hHomotopy).
Local Notation SliceMeasure := (@current_homotopy_slice_weighted_measure R h2 n nu j A U V f g h hHomotopy T hT).
Local Notation hDomain := (@current_map_on_domain R (1+n)%N nu AU V h
  (@current_homotopy_image R n nu A U V f g h geometry)).
Local Notation hBetaRadon := (distribution_representation_radon (normalised_distribution_representation_laws hNT)).

(** Source for [current_homotopy_slice_domain_value]: the
    actual original product point is mapped by h_t,
    supporting the slice integral of Federer 4.1.9,
    p. 363. Both sides stay in the original V. *)
Lemma current_homotopy_slice_domain_value (a:TT) (x:XT):
  hDomain (J (a,x))=SliceMap a x.
Proof.
apply:val_inj.
change (h (set_val (J (a,x)))=h (@euclidean_block_join R 1%N n
  (@euclidean_one_embed R (time a),set_val x))).
by rewrite current_cartesian_domain_join_value euclidean_one_projectK.
Qed.

(** Source for [current_homotopy_slice_scalar_measurable]: every
    continuous original scalar target function pulls back
    measurably by the original h_t, supporting Federer
    4.1.9, p. 363, by 2.3.2 and 3.1.11.
    No compactness of its source support is assumed. *)
Theorem current_homotopy_slice_scalar_measurable (a:TT) (phi:VT->R):
  continuous (phi:VT->real_line_metric R)->
  is_measure_measurable_function beta (real_total_integrand (fun x=>phi (SliceMap a x))).
Proof.
move=>hPhi.
have hSlice:continuous (SliceMap a).
  apply:(@current_map_on_domain_continuous R n nu U V (slice a) (sliceImage a)).
  exact:norm_class_continuous (@current_smooth_homotopy_slice_class R n nu A U V f g h hHomotopy
    (time a) (set_valP a) 0%N).
have hContinuous:continuous (fun x:XT=>(phi (SliceMap a x):real_line_metric R)).
  move=>x;exact:(continuous_comp (hSlice x) (hPhi (SliceMap a x))).
exact:(@continuous_real_integrand_measurable R XT beta hBeta
  (fun B hB=>borel_regular_borel_measurable hBeta (radon_borel_regular hBeta hBetaRadon) hB)
  (fun x=>phi (SliceMap a x)) hContinuous).
Qed.

(** Source for [current_homotopy_slice_density_integral_iff]:
    the actual original weighted image integrates phi
    by the original spatial density product, supporting
    Federer 4.1.9, p. 363, through 2.4.10,
    p. 85, and 2.4.18, pp. 90–91.
    Measurability is required only of this original slice. *)
Theorem current_homotopy_slice_density_integral_iff (a:TT) (phi:VT->R):
  continuous (phi:VT->real_line_metric R)->
  is_measure_measurable_function beta (SliceWeight a)->forall b,
  is_measure_integral (SliceMeasure a) (real_total_integrand phi) b<->
  is_measure_integral beta
    (partial_density_product (real_total_integrand (fun x=>phi (SliceMap a x))) (SliceWeight a)) b.
Proof.
move=>hPhi hWeight b.
pose rho:=measure_with_density beta (SliceWeight a).
have hPositive:=@current_homotopy_slice_weight_nonnegative R h2 n nu j A U V f g h hHomotopy T hT a.
have hRho:is_measure rho:=@measure_with_density_is_measure R XT beta hBeta (SliceWeight a) hPositive.
have hPull:=current_homotopy_slice_scalar_measurable a hPhi.
have hRhoPull:=@measure_density_measurable_function R XT (extended_real_line R) beta rho hBeta
  (SliceWeight a) (real_total_integrand (fun x=>phi (SliceMap a x)))
  (measure_with_density_laws beta (SliceWeight a)) hPositive hPull.
have hPush:=@real_total_pushforward_integral_iff R XT VT rho hRho (SliceMap a) phi hRhoPull b.
have hDensity:=@measure_density_integral_iff R XT beta rho hBeta (SliceWeight a)
  (real_total_integrand (fun x=>phi (SliceMap a x)))
  (measure_with_density_laws beta (SliceWeight a)) hWeight hPositive hPull b.
exact:(iff_trans (iff_sym hPush) hDensity).
Qed.
End CurrentHomotopySliceIntegral.
