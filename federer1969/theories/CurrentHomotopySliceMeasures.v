(** Federer (1969), 4.1.9, p. 363: the actual
    weighted image measure at each original time.
    The density is exactly the printed partial orientation
    weight and uses the established zero-infinity convention.
    Closed-cylinder properness supplies fixed-time support
    properness; no whole-domain properness is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCartesianMap ExteriorGrading ExteriorPowers
  ExteriorMaps ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentMapDifferential CurrentIntegrationCriterion
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopyTimeVelocity CurrentHomotopyCylinder CurrentHomotopySliceProper
  CurrentHomotopyWeightedVariation CurrentProperSupport CurrentProperSupportDomain CurrentProperSupportMapAgreement
  NormalisedCurrentSealed CurrentOrientationSealed CurrentOrientationAlmost
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionPrecomposition PartialFunctionPostcomposition PartialFunctionPair
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensity MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopySliceMeasures.
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

(** Source for [current_homotopy_slice_weight]: the original
    partial norm ||h-dot_t wedge Lambda_j Dh_t(vec T)||
    at fixed time, Federer 4.1.9, p. 363. This
    is exactly the original product weight restricted to
    that time; the orientation domain is retained. *)
Definition current_homotopy_slice_weight (a:TT):partial_function XT (extended_real_line R):=
  partial_function_precompose (fun x:XT=>J (a,x)) W.

(** Source for [current_homotopy_slice_weight_graph]: the
    fixed-time density has exactly the printed norm and
    original orientation graph, supporting the slice image
    measures in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_slice_weight_graph (a:TT) (x:XT) w:
  partial_function_graph (current_homotopy_slice_weight a) x w <->
    exists xi,partial_function_graph OT x xi /\ (MassValue a x xi)%:E=w.
Proof.
change ((exists za:CT*exterior_power X j,
  (J (a,x)=za.1 /\partial_function_graph OT (D (J (a,x))).2 za.2) /\
    (MassValue (D za.1).1 (D za.1).2 za.2)%:E=w)<->
  exists xi,partial_function_graph OT x xi /\(MassValue a x xi)%:E=w).
split.
- move=>[[z xi] [[hZ hXi] hValue]].
  change (J (a,x)=z) in hZ;subst z.
  rewrite current_cartesian_domain_join_split in hXi hValue.
  exists xi;by split.
- move=>[xi [hXi hValue]];exists (J (a,x),xi);split.
  + split;first by [].
    by rewrite current_cartesian_domain_join_split.
  + by rewrite current_cartesian_domain_join_split.
Qed.

(** Source for [current_homotopy_slice_weight_nonnegative]:
    the exact partial slice weight is nonnegative on its
    original conull domain for every original time,
    supporting Federer 4.1.9, p. 363. *)
Theorem current_homotopy_slice_weight_nonnegative (a:TT):
  measure_almost_everywhere beta (partial_extended_nonnegative_locus (current_homotopy_slice_weight a)).
Proof.
apply:(@measure_almost_everywhere_mono R XT beta hBeta _ _ _
  (@current_orientation_normalised_agreement R h2 n j U hU T hT))=>x hx.
exists (MassValue a x (eta x))%:E;split.
- apply:(@current_homotopy_slice_weight_graph a x _).2;exists (eta x);by split.
- rewrite lee_fin;exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 nu (1+j)).1 _.
Qed.

(** Source for [current_homotopy_slice_domain_map]: the actual
    original map h_t on relative source and target domains,
    supporting the slice image measure in Federer 4.1.9,
    p. 363. No point outside V is introduced. *)
Definition current_homotopy_slice_domain_map (a:TT):XT->VT:=
  @current_map_on_domain R n nu U V (slice a) (sliceImage a).

(** Source for [current_homotopy_slice_weighted_measure]: the
    literal image (h_t)#(||T|| restricted by the printed
    partial norm weight), Federer 4.1.9, p. 363.
    The original density and image measures remain opaque. *)
Definition current_homotopy_slice_weighted_measure (a:TT):set VT->\bar R:=
  measure_pushforward (current_homotopy_slice_domain_map a)
    (measure_with_density beta (current_homotopy_slice_weight a)).

(** Source for [current_homotopy_slice_weighted_measure_laws]:
    every original weighted slice image is an actual measure,
    supporting Federer 4.1.9, p. 363. Neither finite
    total mass nor totality of the orientation is imposed. *)
Theorem current_homotopy_slice_weighted_measure_laws (a:TT):
  is_measure (current_homotopy_slice_weighted_measure a).
Proof.
apply:measure_pushforward_is_measure.
exact:(@measure_with_density_is_measure R XT beta hBeta (current_homotopy_slice_weight a)
  (current_homotopy_slice_weight_nonnegative a)).
Qed.

(** Source for [current_homotopy_slice_original_proper]: the
    single original cylinder hypothesis gives support
    properness of h_t for every t in [0,1], supporting
    the slice images in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_slice_original_proper (a:TT) (hBand:0<=time a<=1):
  @is_current_homotopy_proper R h2 n nu j A U V f g h geometry T->
  @is_current_proper_on_support R h2 n nu j U hU V T (slice a) (sliceImage a).
Proof.
move=>hp.
apply:(@current_proper_support_map_agreement R h2 n nu j U V hU T (slice a) (slice a)
  (@current_homotopy_band_slice_image R n nu A U V f g h geometry (time a) hBand)
  (sliceImage a) (fun _ _=>erefl _)).
exact:(@current_homotopy_slice_proper R h2 n nu j A U V f g h geometry T (time a) hBand hp).
Qed.
End CurrentHomotopySliceMeasures.
