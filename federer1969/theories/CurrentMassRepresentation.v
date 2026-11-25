(** Federer (1969), 4.1.7, p. 358: the
    exact original mass identity for every
    integration-representable current, including infinite
    masses and empty domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentDomainGeometry CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionVariationUP
  NormalisedDistributionRepresentationUP NormalisedDistributionTotalMass CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentMassSealed CurrentMassBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentMassRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_normalised_mass_total]: the
    original mass equals the total Radon
    measure in any normalized original representation,
    Federer 4.1.7, p. 358. *)
Theorem current_normalised_mass_total (T:C) (mu:set UT->\bar R) (k:UT->V):
  @is_normalised_current_representation R h2 n m U hU T mu k->M T=mu setT.
Proof.
move=>hRepresentation.
have hMeasure:=@normalised_distribution_total_mass R UT
  (@current_domain_locally_compact R n U hU) Y NY hNY V ed DN hDual O hO DT dvalues
  (action T) mu k hRepresentation.
exact:(distribution_variation_value_unique
  (@current_mass_majorant_one R h2 n m U hU T) hMeasure).
Qed.

(** Source for [current_represented_mass_total]: the
    original statement M(T)=||T||(U) for
    every represented current, Federer 4.1.7,
    p. 358. No finiteness is assumed. *)
Theorem current_represented_mass_total (T:C)
    (hT:@is_integration_representable_current R h2 n m U hU T):
  M T=(@NormalisedCurrent.measure R h2 n m U hU T hT) setT.
Proof.
exact:(@current_normalised_mass_total T (@NormalisedCurrent.measure R h2 n m U hU T hT)
  (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT)
  (@NormalisedCurrent.laws R h2 n m U hU T hT)).
Qed.
End CurrentMassRepresentation.
