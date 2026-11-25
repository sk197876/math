(** Federer (1969), 4.1.11, p. 365: specialize the
    original join estimate to delta_c. The existing point
    current is represented by the original unit point mass
    and scalar unit, as in 4.1.7, pp. 356, 359. Measures
    remain on the actual open domain, without ambient extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingZero AlternatingPairing
  CurrentDomain CurrentDomainGeometry SubtypeCompactHausdorff CurrentSpaces CurrentCoefficientNorms
  CurrentDiracDensity CurrentDirac CurrentZeroDegreeExteriorLaws CurrentConstantRadonDensity
  OpenCurrentDensityUP CurrentIntegrationCriterion CurrentUnitRepresentationVariation NormalisedCurrentSealed
  CurrentMultivectorDual MultivectorDualSealed BoundedCurrentDensityUniqueness
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP DistributionVariationDomain
  DistributionIntegralFieldUP MeasureUP RadonMeasureUP PointMassMeasure PointMassRadon PointMassIntegral
  MeasureAlmostUP MeasureAlmostBasic SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDiracRadonRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Variable c:X.
Hypothesis hc:U c.
Local Notation UT := (current_domain R n U).
Local Notation D := (@dirac_current R h2 n U hU c).
Local Notation unit := (@current_scalar_multivector_unit R n).

(** Source for [current_dirac_domain_point]: the original
    point c regarded as a point of its given open domain,
    supporting Federer 4.1.11, p. 365. This is only the
    existing subtype inclusion, with no chosen point. *)
Definition current_dirac_domain_point:UT:=exist _ c (mem_set hc).
Local Notation cU := current_dirac_domain_point.
Local Notation gamma := (point_mass R cU).
Local Notation hm := (point_mass_is_measure R cU).

(** Source for [current_dirac_measure_radon]: the original
    point mass on U is Radon, supporting the point-cone
    specialization in Federer 4.1.11, p. 365. *)
Theorem current_dirac_measure_radon:is_radon_measure gamma.
Proof.
apply:point_mass_radon;last exact:(@current_domain_locally_compact R n U hU).
exact:(@set_type_hausdorff (real_norm_metric_space hNX) U
  (@metric_hausdorff R (real_norm_metric_space hNX))).
Qed.

(** Source for [current_dirac_unit_mass]: the scalar-unit
    density of delta_c has mass one, supporting Federer
    4.1.11, p. 365, with the degree-zero convention of
    1.3.1, p. 13, and 4.1.7, pp. 356–357. *)
Theorem current_dirac_unit_mass:@current_vector_mass R h2 n 0%N unit = 1.
Proof. by rewrite /current_scalar_multivector_unit current_vector_mass_zeroth_scalar normr1. Qed.

(** Source for [current_dirac_radon_representation]: the
    original delta_c is represented by the actual unit point
    mass and constant exterior unit, supporting Federer
    4.1.11, p. 365, by the original pairing definition of
    4.1.7, pp. 356, 359. Every original test is retained. *)
Theorem current_dirac_radon_representation:
  @is_current_integration_representation R h2 n 0%N U hU D gamma (fun _=>unit).
Proof.
have hField:=@current_constant_radon_density_integrable R h2 n 0%N U gamma hm
  current_dirac_measure_radon unit.
constructor;[exact:hm|exact:current_dirac_measure_radon|exact:hField.1|exact:hField.2|].
move=>psi.
have hValue:=@point_mass_real_integral R UT cU
  (fun x=>@MultivectorDual.evaluation R X 0%N unit
    (@current_test_value R h2 n U hU 0%N psi (set_val x))).
rewrite MultivectorDual.laws current_scalar_multivector_unit_pairing
  -dirac_current_evaluation in hValue.
exact:hValue.
Qed.

(** Source for [current_dirac_representable]: the original
    point current is representable by integration, supporting
    the cone estimate in Federer 4.1.11, p. 365. *)
Theorem current_dirac_representable:
  @is_integration_representable_current R h2 n 0%N U hU D.
Proof. exists gamma,(fun _=>unit);exact:current_dirac_radon_representation. Qed.

(** Source for [current_dirac_variation]: the original
    variation of delta_c is the actual unit point mass on
    every set, supporting Federer 4.1.11, p. 365. The
    conclusion permits every representability witness. *)
Theorem current_dirac_variation
    (hD:@is_integration_representable_current R h2 n 0%N U hU D):
  @NormalisedCurrent.measure R h2 n 0%N U hU D hD=gamma.
Proof.
exact:(@current_unit_representation_variation R h2 n 0%N U hU D gamma (fun _=>unit)
  current_dirac_radon_representation (fun _=>current_dirac_unit_mass) hD).
Qed.

(** Source for [current_dirac_density_agreement]: the
    actual auxiliary density of delta_c is the scalar unit
    almost everywhere for its original variation, supporting
    Federer 4.1.11, p. 365. This does not change the
    original maximal partial orientation. *)
Theorem current_dirac_density_agreement
    (hD:@is_integration_representable_current R h2 n 0%N U hU D):
  measure_almost_everywhere (@NormalisedCurrent.measure R h2 n 0%N U hU D hD)
    [set x|@NormalisedCurrent.auxiliary_density R h2 n 0%N U hU D hD x=unit].
Proof.
have hNormal:=@NormalisedCurrent.laws R h2 n 0%N U hU D hD.
have hBase:=normalised_distribution_representation_laws hNormal.
have hRep:=current_dirac_radon_representation.
rewrite (current_dirac_variation hD) in hBase *.
  have hUnit (x:UT):@current_vector_mass R h2 n 0%N unit <= 1 by rewrite current_dirac_unit_mass.
exact:(@bounded_current_density_almost_unique R h2 n 0%N U hU gamma hm
  current_dirac_measure_radon
  (@NormalisedCurrent.auxiliary_density R h2 n 0%N U hU D hD) (fun _=>unit)
  (distribution_representation_weak_measurable hBase)
  (distribution_representation_weak_measurable hRep)
  (normalised_distribution_density_unit_bound hNormal) hUnit
  (@current_value R h2 n U hU 0%N D)
  (distribution_representation_action hBase) (distribution_representation_action hRep)).
Qed.
End CurrentDiracRadonRepresentation.
