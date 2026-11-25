(** Federer (1969), 4.1.11, pp. 364–365: the
    original S times ([0,1] times T) has its actual
    Cartesian Radon representation. These aliases retain
    the two original variation measures and their densities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentCartesianDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianDensityMeasurable CurrentCartesianProductSealed CurrentCartesianOriginalDensity
  CurrentCartesianVariationUpper CurrentJoinDomain CurrentJoinTimeRepresentation
  CurrentJoinTimeProductRepresentation OpenCurrentDensityUP
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinRawRepresentation.
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
Local Notation InnerDomain := (current_domain R (1+n)%N TimeSpace).
Local Notation CT := (current_domain R (n+(1+n))%N Domain).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j Time Full hTime hFull Segment T).
Local Notation hInner := (@current_join_time_product_representable R h2 n j Full hFull T hT).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  Full TimeSpace hFull hTimeSpace S Inner).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n i Full hFull S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n i Full hFull S hS).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation hNS := (@NormalisedCurrent.laws R h2 n i Full hFull S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNS)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).

(** Source for [current_join_raw_measure]: the original
    product variation measure before applying F, supporting
    Federer 4.1.11, p. 365. The inner measure equals
    the time-spatial product by the preceding simplicity law. *)
Definition current_join_raw_measure:set CT->\bar R:=
  @CartesianCurrentMeasure.value R n (1+n)%N Full TimeSpace alpha beta hAlpha hBeta.

(** Source for [current_join_raw_density]: the actual
    original Cartesian density of S times ([0,1] times T),
    supporting the first mass estimate in Federer 4.1.11,
    p. 365. It is not assumed to have mass one. *)
Definition current_join_raw_density:CT->exterior_power (R_n R (n+(1+n))%N) (i+(1+j))%N:=
  @current_cartesian_density R n (1+n)%N i (1+j)%N Full TimeSpace xi eta.

(** Source for [current_join_raw_representation]: the
    actual source current has its original Radon product
    representation, supporting Federer 4.1.11, p. 365,
    through the original representation theorem of 4.1.8. *)
Theorem current_join_raw_representation:
  @is_current_integration_representation R h2 (n+(1+n))%N (i+(1+j))%N Domain hDomain
    Raw current_join_raw_measure current_join_raw_density.
Proof.
exact:(@current_cartesian_original_representation R h2 n (1+n)%N i (1+j)%N
  Full TimeSpace hFull hTimeSpace S Inner hS hInner).
Qed.

(** Source for [current_join_raw_representable]: the
    original source current is representable by integration,
    supporting the sharp join bound in Federer 4.1.11, p. 365. *)
Theorem current_join_raw_representable:
  @is_integration_representable_current R h2 (n+(1+n))%N (i+(1+j))%N Domain hDomain Raw.
Proof. exists current_join_raw_measure,current_join_raw_density;exact:current_join_raw_representation. Qed.

(** Source for [current_join_raw_density_locally_integrable]:
    the original source density is locally mass-integrable,
    supporting Federer 4.1.11, p. 365. This is the
    already proved compact-integrability part of its representation. *)
Theorem current_join_raw_density_locally_integrable:
  @is_locally_integrable_open_current_density R h2 (n+(1+n))%N (i+(1+j))%N Domain
    current_join_raw_measure current_join_raw_density.
Proof.
exact:conj (distribution_representation_weak_measurable current_join_raw_representation)
  (distribution_representation_compact_norm current_join_raw_representation).
Qed.

(** Source for [current_join_raw_density_unit_bound]: the
    original source density is everywhere bounded by one
    in mass, supporting its exact measurable image in
    Federer 4.1.11, p. 365. No simplicity is imposed on S or T. *)
Theorem current_join_raw_density_unit_bound z:
  @current_vector_mass R h2 (n+(1+n))%N (i+(1+j))%N (current_join_raw_density z)<=1.
Proof.
exact:(@current_cartesian_product_density_unit_bound R h2 n (1+n)%N i (1+j)%N
  Full TimeSpace hFull hTimeSpace S Inner alpha beta xi eta hNS hNT z).
Qed.
End CurrentJoinRawRepresentation.
