(** Federer (1969), 4.1.11, p. 365: identify the
    exact source image density with the two original
    spatial orientations. The time-product equality and
    the original Cartesian conull laws supply the comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  ExteriorGrading ExteriorMaps CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentOrientationAlmost
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed
  CurrentCartesianMeasureRadon CurrentCartesianMeasureAlmost CurrentCartesianVectorProduct
  CurrentCartesianProductSealed CurrentJoinDomain CurrentJoinRawCoordinates CurrentJoinRawRepresentation
  CurrentJoinTimeRepresentation CurrentJoinTimeProductRepresentation CurrentJoinMapSealed
  CurrentJoinExteriorDifferential CurrentJoinOriginalWeight CurrentMapDifferential CurrentImageDensityPairing
  EuclideanOneCoordinate EuclideanBlockLinearMaps EuclideanScalarCoordinateMaps
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinRawDensityAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace := (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Local Notation XT := (current_domain R n Full).
Local Notation TT := (current_domain R 1%N Time).
Local Notation IT := (current_domain R (1+n)%N TimeSpace).
Local Notation CT := (current_domain R (n+(1+n))%N Domain).
Local Notation D := (@CartesianCurrentDomain.split R n (1+n)%N Full TimeSpace).
Local Notation E := (@CartesianCurrentDomain.split R 1%N n Time Full).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_representable R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j Time Full hTime hFull Segment T).
Local Notation hInner := (@current_join_time_product_representable R h2 n j Full hFull T hT).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n i Full hFull S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j Full hFull T hT).
Local Notation rho := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation gamma := (@NormalisedCurrent.measure R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n i Full hFull S hS).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j Full hFull T hT).
Local Notation theta := (@NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation hNS := (@NormalisedCurrent.laws R h2 n i Full hFull S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j Full hFull T hT).
Local Notation hNI := (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation hNP := (@NormalisedCurrent.laws R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNS)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation hRho := (distribution_representation_measure (normalised_distribution_representation_laws hNI)).
Local Notation hGamma := (distribution_representation_measure (normalised_distribution_representation_laws hNP)).
Local Notation lambda := (@current_join_raw_measure R h2 n i j S T hS hT).
Local Notation hLambda := (distribution_representation_measure
  (@current_join_raw_representation R h2 n i j S T hS hT)).
Local Notation zeta := (@current_join_raw_density R h2 n i j S T hS hT).
Local Notation OS := (@CurrentOrientation.value R h2 n i Full hFull S hS).
Local Notation OT := (@CurrentOrientation.value R h2 n j Full hFull T hT).
Local Notation first := (@current_join_first_point R n).
Local Notation last := (@current_join_last_point R n).
Local Notation velocity := (@current_join_time_vector R).

(** Source for [current_join_raw_inner_density_agreement]:
    the inner normalized density is the original positive
    time vector times the spatial density for almost every
    point of its own variation, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_raw_inner_density_agreement:
  measure_almost_everywhere gamma [set u:IT|theta u=
    @current_cartesian_vector_product R 1%N n 1%N j velocity (eta (E u).2)].
Proof.
have h:=@current_join_time_product_density_agreement R h2 n j Full hFull T hT hInner.
by rewrite -(@current_join_time_product_variation R h2 n j Full hFull T hT hInner) in h.
Qed.

(** Source for [current_join_raw_factor_orientations]: the
    actual original S and T orienting fields agree with
    their auxiliary densities on a conull subset of the
    original source measure, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_raw_factor_orientations:
  measure_almost_everywhere lambda [set z:CT|
    partial_function_graph OS (first z) (xi (first z)) /\
    partial_function_graph OT (last z) (eta (last z))].
Proof.
have hFirst:=@current_cartesian_measure_first_almost R n (1+n)%N Full TimeSpace
  alpha gamma hAlpha hGamma _ (@current_orientation_normalised_agreement R h2 n i Full hFull S hS).
have hInnerT:=@current_cartesian_measure_second_almost R 1%N n Time Full rho beta hRho hBeta _
  (@current_orientation_normalised_agreement R h2 n j Full hFull T hT).
rewrite -(@current_join_time_product_variation R h2 n j Full hFull T hT hInner) in hInnerT.
have hLast:=@current_cartesian_measure_second_almost R n (1+n)%N Full TimeSpace
  alpha gamma hAlpha hGamma _ hInnerT.
exact:(measure_almost_everywhere_and hLambda hFirst hLast).
Qed.

(** Source for [current_join_raw_exterior_image]: the actual
    exterior image of the original source density equals
    the exact printed three-factor vector almost everywhere,
    supporting Federer 4.1.11, p. 365, first mass display. *)
Theorem current_join_raw_exterior_image:
  measure_almost_everywhere lambda [set z:CT|
    @current_image_density R (n+(1+n))%N n (i+(1+j))%N Domain (@CurrentJoinMap.value R n) zeta z=
      @current_join_original_vector R n i j z (xi (first z)) (eta (last z))].
Proof.
have hInnerOnSource:=@current_cartesian_measure_second_almost R n (1+n)%N Full TimeSpace
  alpha gamma hAlpha hGamma _ current_join_raw_inner_density_agreement.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _ hInnerOnSource)=>z hInnerEq.
change (exterior_power_map (hom_as_linear (@current_map_differential R (n+(1+n))%N n Domain
  (@CurrentJoinMap.value R n) (set_val z))) (i+(1+j))%N
  (@current_cartesian_vector_product R n (1+n)%N i (1+j)%N (xi (first z)) (theta (D z).2))=
  @current_join_original_vector R n i j z (xi (first z)) (eta (last z))).
rewrite hInnerEq (@current_join_time_vector_value R).
have hImage:=@current_join_exterior_differential R n Domain hDomain (set_val z) (set_valP z)
  i j (xi (first z)) (eta (last z)).
have [hFirst [hTime hLast]]:=@current_join_raw_coordinate_values R n z.
rewrite hFirst hTime hLast in hImage.
exact:hImage.
Qed.
End CurrentJoinRawDensityAgreement.
