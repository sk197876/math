(** Federer (1969), 4.1.9, p. 363: the displayed
    almost-everywhere exterior-image identity for the actual
    represented time product. Both original orienting fields
    keep their partial domains. The pointwise exterior
    differential identity supplies the printed velocity wedge. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentMapDifferential CurrentCartesianDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianVectorProduct CurrentCartesianProductSealed CurrentCartesianOriginalDensity CurrentHomotopyProductOrientation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity CurrentHomotopyTimeVelocity CurrentHomotopyExteriorDifferential
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopyOriginalImage.
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
Local Notation Product := (@current_cartesian_vector_product R 1%N n 1%N j).
Local Notation DH z := (@current_map_differential R (1+n)%N nu AU h (set_val z)).
Local Notation DS z := (@current_map_differential R n nu U (@current_homotopy_slice_map R n nu h (time z)) (space z)).
Local Notation Velocity z := (@current_homotopy_time_velocity R n nu A U h (time z) (space z)).

(** Source for [current_homotopy_original_product_representable]:
    the original [0,1] times T is representable whenever
    T is, supporting the last paragraph of Federer
    4.1.9, p. 363. No finite mass is added. *)
Theorem current_homotopy_original_product_representable:
  @is_integration_representable_current R h2 (1+n)%N (1+j) AU hAU P.
Proof.
exact:(@current_cartesian_original_representable R h2 1%N n 1%N j AT U hAT hU S T hS hT).
Qed.

(** Source for [current_homotopy_original_exterior_image]:
    Lambda_(1+j) Dh applied to the actual original product
    orientation equals h-dot_t wedged with Lambda_j Dh_t
    applied to the original orientation of T almost
    everywhere for the original product variations, Federer
    4.1.9, p. 363. Every partial graph is retained. *)
Theorem current_homotopy_original_exterior_image
    (hP:@is_integration_representable_current R h2 (1+n)%N (1+j) AU hAU P):
  measure_almost_everywhere lambda [set z:CT|exists eta,exists theta,
    partial_function_graph OT (D z).2 eta /\
    partial_function_graph (@CurrentOrientation.value R h2 (1+n)%N (1+j) AU hAU P hP) z theta /\
    exterior_power_map (hom_as_linear (DH z)) (1+j) theta=
      exterior_product (exterior_first_inclusion Y (Velocity z))
        (exterior_power_map (hom_as_linear (DS z)) j eta)].
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (@current_homotopy_product_orientation R h2 n j A hInterval U hU T hT hP))
  =>z [eta [hEta hProduct]].
exists eta,(Product velocity eta);split;first exact:hEta.
split;first exact:hProduct.
have hJoin:Point (time z) (space z)=set_val z.
  rewrite euclidean_one_projectK.
  rewrite -(@current_cartesian_domain_join_value R 1%N n AT U (D z)).
  by rewrite current_cartesian_domain_split_join.
have hTime:A (time z):=set_valP (D z).1.
have hSpace:U (space z):=set_valP (D z).2.
have hClass:@is_current_homotopy_class R n nu A U V f g h 1%N:=conj geometry (hHomotopy.2 1%N).
have hEqual:=@current_homotopy_exterior_differential R n nu j A U V f g h hClass
  (time z) (space z) eta hTime hSpace.
by rewrite hJoin in hEqual.
Qed.
End CurrentHomotopyOriginalImage.
