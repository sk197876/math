(** Federer (1969), 4.1.11, p. 365: the original
    time-space factor has exact product variation because
    only its time vector needs to be simple. The current
    in the spatial factor remains arbitrary and representable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentCartesianDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianMeasureAlmost CurrentCartesianVectorProduct CurrentCartesianDensityMeasurable
  CurrentCartesianProductSealed CurrentCartesianOriginalDensity CurrentCartesianVariationComparison
  CurrentCartesianVariationUpper BoundedCurrentDensityUniqueness CurrentJoinDomain
  CurrentJoinTimeRepresentation SimpleVectors DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinTimeProductRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation TT := (current_domain R 1%N Time).
Local Notation UT := (current_domain R n U).
Local Notation TimeU := (@euclidean_cartesian_set R 1%N n Time U).
Local Notation hTimeU := (@current_cartesian_domain_open R 1%N n Time U hTime hU).
Local Notation CT := (current_domain R (1+n)%N TimeU).
Local Notation D := (@CartesianCurrentDomain.split R 1%N n Time U).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_representable R h2).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime I hI).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 1%N 1%N Time hTime I hI).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j U hU T hT).
Local Notation hNI := (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime I hI).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j U hU T hT).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNI)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation lambda := (@CartesianCurrentMeasure.value R 1%N n Time U alpha beta hAlpha hBeta).
Local Notation hLambda := (@current_cartesian_measure_is_measure R 1%N n Time U alpha beta hAlpha hBeta).
Local Notation P := (@CartesianCurrentProduct.value R h2 1%N n 1%N j Time U hTime hU I T).
Local Notation zeta := (@current_cartesian_density R 1%N n 1%N j Time U xi eta).
Local Notation velocity := (@current_join_time_vector R).

(** Source for [current_join_time_product_representable]:
    the actual [0,1] times T is representable under its
    original product density, supporting the sharp join
    estimate in Federer 4.1.11, p. 365. *)
Theorem current_join_time_product_representable:
  @is_integration_representable_current R h2 (1+n)%N (1+j)%N TimeU hTimeU P.
Proof.
exact:(@current_cartesian_original_representable R h2 1%N n 1%N j Time U hTime hU I T hI hT).
Qed.

(** Source for [current_join_time_product_time_agreement]:
    the positive time density agrees on a conull set of
    the original product measure, supporting Federer 4.1.11,
    p. 365, without a finite-mass assumption on T. *)
Theorem current_join_time_product_time_agreement:
  measure_almost_everywhere lambda [set z:CT|xi (D z).1=velocity].
Proof.
exact:(@current_cartesian_measure_first_almost R 1%N n Time U alpha beta hAlpha hBeta _
  (@current_join_time_density_agreement R h2 hI)).
Qed.

(** Source for [current_join_time_product_simple]: only
    the original time density supplies the either-simple
    hypothesis of 4.1.8, p. 361, supporting the mass
    computation in Federer 4.1.11, p. 365. *)
Theorem current_join_time_product_simple:
  measure_almost_everywhere lambda [set z:CT|simple (xi (D z).1) \/simple (eta (D z).2)].
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  current_join_time_product_time_agreement)=>z hz.
left;rewrite hz;exact:(@current_join_time_vector_simple R).
Qed.

(** Source for [current_join_time_product_variation]: the
    original time-product variation equals the product of
    the original time and spatial variations on every set,
    supporting Federer 4.1.11, p. 365, through 4.1.8. *)
Theorem current_join_time_product_variation
    (hP:@is_integration_representable_current R h2 (1+n)%N (1+j)%N TimeU hTimeU P):
  @NormalisedCurrent.measure R h2 (1+n)%N (1+j)%N TimeU hTimeU P hP=lambda.
Proof.
exact:(@current_cartesian_product_variation_simple_equality R h2 1%N n 1%N j Time U hTime hU
  I T alpha beta xi eta hNI hNT hP current_join_time_product_simple).
Qed.

(** Source for [current_join_time_product_density_agreement]:
    the actual time-product density is the positive time
    vector wedged with the original spatial auxiliary
    density almost everywhere for the exact product measure,
    supporting Federer 4.1.11, p. 365. *)
Theorem current_join_time_product_density_agreement
    (hP:@is_integration_representable_current R h2 (1+n)%N (1+j)%N TimeU hTimeU P):
  measure_almost_everywhere lambda [set z:CT|
    @NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j)%N TimeU hTimeU P hP z=
      @current_cartesian_vector_product R 1%N n 1%N j velocity (eta (D z).2)].
Proof.
have hRep:=@current_cartesian_original_representation R h2 1%N n 1%N j Time U hTime hU I T hI hT.
have hNormal:=@NormalisedCurrent.laws R h2 (1+n)%N (1+j)%N TimeU hTimeU P hP.
have hBase:=normalised_distribution_representation_laws hNormal.
rewrite (current_join_time_product_variation hP) in hBase.
have hBound:=@current_cartesian_product_density_unit_bound R h2 1%N n 1%N j Time U hTime hU
  I T alpha beta xi eta hNI hNT.
have hUnique:=@bounded_current_density_almost_unique R h2 (1+n)%N (1+j)%N TimeU hTimeU
  lambda hLambda (distribution_representation_radon hRep)
  (@NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j)%N TimeU hTimeU P hP) zeta
  (distribution_representation_weak_measurable hBase) (distribution_representation_weak_measurable hRep)
  (normalised_distribution_density_unit_bound hNormal) hBound
  (@current_value R h2 (1+n)%N TimeU hTimeU (1+j)%N P)
  (distribution_representation_action hBase) (distribution_representation_action hRep).
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda hUnique current_join_time_product_time_agreement))=>z [hEq hTimeEq].
change (@NormalisedCurrent.auxiliary_density R h2 (1+n)%N (1+j)%N TimeU hTimeU P hP z=
  @current_cartesian_vector_product R 1%N n 1%N j velocity (eta (D z).2)).
by rewrite hEq /current_cartesian_density hTimeEq.
Qed.
End CurrentJoinTimeProductRepresentation.
