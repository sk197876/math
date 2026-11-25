(** Federer (1969), 4.1.11, p. 365: apply the
    sharp proper-image mass inequality to the original
    source current. Equal degree expressions change no
    mass, and compact support supplies actual properness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentDegreeTransport CurrentDegreeTransportSupport CurrentPushforwardDegreeTransport
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed CurrentMassSealed
  CurrentMassDegreeTransport CurrentImageDensityPairing CurrentImageWeightRadon
  CurrentRepresentedPushforwardMass CurrentJoinDomain CurrentJoinSourceChain CurrentJoinSourceCompact
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinSealed CurrentJoinLaws CurrentJoinRawRepresentation
  DistributionIntegrationRepresentationUP MeasureUP MeasureAlmostUP RadonMeasureUP
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinRawMass.
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
Local Notation CT := (current_domain R (n+(1+n))%N Domain).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull j T).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j Time Full hTime hFull Segment T).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  Full TimeSpace hFull hTimeSpace S Inner).
Local Notation Chain := (@current_join_source_chain R h2 n i j S T).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth := (@current_join_map_smooth R n Domain hDomain).

(** Source for [current_join_raw_compact]: the original
    source product has compact support before its equal-
    degree identification, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_raw_compact:
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
    (@current_support R h2 (n+(1+n))%N Domain hDomain (i+(1+j))%N Raw).
Proof.
have h:=@current_join_source_compact R h2 n i j S T hS hT.
by rewrite /current_join_source_chain current_degree_transport_support in h.
Qed.

(** Source for [current_join_raw_proper]: the original F
    is proper on the compact source-current support,
    supporting the first mass display in Federer 4.1.11, p. 365. *)
Definition current_join_raw_proper:
  @is_current_proper_on_support R h2 (n+(1+n))%N n (i+(1+j))%N
    Domain hDomain Full Raw F Image:=
  @current_compact_map_proper R h2 (n+(1+n))%N n (i+(1+j))%N
    Domain Full hDomain Raw F Image (norm_class_continuous (Smooth 0%N)) current_join_raw_compact.

Local Notation push := (@CurrentPushforward.value R h2 (n+(1+n))%N n (i+(1+j))%N
  Domain Full hDomain hFull Raw F Image Smooth current_join_raw_proper).
Local Notation J := (@CurrentJoin.value R h2 n i j S T hS hT).

(** Source for [current_join_raw_image]: the original join
    is exactly F# of its source product under the canonical
    degree identification, supporting Federer 4.1.11, p. 365.
    Both properness witnesses concern the same compact support. *)
Theorem current_join_raw_image:
  J=@current_degree_transport R h2 n Full hFull (i+(1+j))%N (i+1+j)%N (addnA i 1%N j) push.
Proof.
rewrite current_join_pushforward.
exact:esym (@current_pushforward_degree_transport R h2 (n+(1+n))%N n Domain Full
  hDomain hFull F Image Smooth (i+(1+j))%N (i+1+j)%N (addnA i 1%N j) Raw
  current_join_raw_proper (@current_join_source_proper R h2 n i j S T hS hT)).
Qed.

Hypothesis hRS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hRT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation lambda := (@current_join_raw_measure R h2 n i j S T hRS hRT).
Local Notation zeta := (@current_join_raw_density R h2 n i j S T hRS hRT).
Local Notation hRep := (@current_join_raw_representation R h2 n i j S T hRS hRT).
Local Notation hRaw := (@current_join_raw_representable R h2 n i j S T hRS hRT).
Local Notation hLambda := (distribution_representation_measure hRep).
Local Notation hRadon := (distribution_representation_radon hRep).
Local Notation W := (real_total_integrand (fun z:CT=>@current_vector_mass R h2 n (i+(1+j))%N
  (@current_image_density R (n+(1+n))%N n (i+(1+j))%N Domain F zeta z))).

(** Source for [current_join_raw_mass_integral]: the exact
    exterior-image weight has a nonnegative original source
    integral, supporting Federer 4.1.11, p. 365. Positive
    infinity remains a permitted integral value. *)
Theorem current_join_raw_mass_integral:
  is_measure_integral lambda W (measure_lower_integral lambda W).
Proof.
exact:(@nonnegative_measurable_function_integral R CT lambda hLambda W
  (@current_image_weight_measurable R h2 (n+(1+n))%N n (i+(1+j))%N
    Domain Full hDomain hFull F Image Smooth lambda hLambda hRadon zeta
    (@current_join_raw_density_unit_bound R h2 n i j S T hRS hRT)
    (distribution_representation_weak_measurable hRep))
  (@current_image_weight_nonnegative R h2 (n+(1+n))%N n (i+(1+j))%N Domain F lambda hLambda zeta)).1.
Qed.

(** Source for [current_join_raw_mass_bound]: the original
    join mass is bounded by the integral of its exact
    exterior-image density, supporting the first mass display
    in Federer 4.1.11, p. 365, through 4.1.7, p. 359. *)
Theorem current_join_raw_mass_bound a:is_measure_integral lambda W a->
  (@CurrentMass.value R h2 n (i+1+j)%N Full hFull J<=a)%E.
Proof.
move=>hIntegral;rewrite current_join_raw_image current_mass_degree_transport.
exact:(@current_represented_pushforward_mass_bound R h2 (n+(1+n))%N n (i+(1+j))%N
  Domain Full hDomain hFull lambda hLambda hRadon zeta
  (@current_join_raw_density_locally_integrable R h2 n i j S T hRS hRT) Raw hRep hRaw
  F Image Smooth current_join_raw_proper a hIntegral).
Qed.
End CurrentJoinRawMass.
