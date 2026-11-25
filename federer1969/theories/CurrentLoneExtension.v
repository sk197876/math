(** Federer (1969), 4.1.7, pp. 356–357:
    use the original current's unique L1
    extension from 4.1.5, p. 350.
    The actual mass/comass dual spaces discharge
    its analytic hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentDomain
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  CurrentIntegrationCriterion CurrentOriginalBallFormula SmoothFunctionSpaceUP SmoothTestEvaluation
  DistributionVariationDomain DistributionLoneExtension DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureLpMembershipUP SummableRealFunctionUP
  DualLoneIntegralUP DualLoneIntegralSealed DualLoneIntegralAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLoneExtension.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hD := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Variable T:@current_space R h2 n U hU m.
Variable mu:set UT->\bar R.
Variable eta:UT->V.
Hypothesis hRepresentation:@is_normalised_current_representation R h2 n m U hU T mu eta.
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation).

(** Source for [current_original_test_lone_member]:
    every original current test belongs to
    L1(||T||), Federer 4.1.7, pp. 356–357,
    by the original density theorem in 4.1.5. *)
Lemma current_original_test_lone_member (psi:DT):
  is_measure_lp_function mu 1 (partial_function_total
    (fun x:UT=>(@current_test_value R h2 n U hU m psi (set_val x):real_norm_metric_space hNY))).
Proof.
exact:(@distribution_original_test_lone_member R n Y NY hNY
  (@current_form_separable R h2 n m)
  U E ev hE (@current_value R h2 n U hU m T) V ed VN hD O hO mu eta hRepresentation psi).
Qed.

(** Source for [current_representation_lone_total_action]:
    the actual original L1 extension integrates
    every total summable covector field against
    the original density, Federer 4.1.7,
    pp. 356–357, through 4.1.5, p. 350. *)
Lemma current_representation_lone_total_action (f:UT->Y):
  is_measure_lp_function mu 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) ->
  is_measure_integral mu (real_total_integrand (fun x=>ed (eta x) (f x)))
    (I (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))))%:E.
Proof.
exact:(@dual_lone_integral_total_action R UT Y NY hNY V ed eta mu I
  (@DualLoneIntegral.laws R UT Y NY hNY (@current_form_separable R h2 n m)
    V ed VN hD O hO mu (distribution_representation_measure hBase) eta
    (distribution_representation_weak_measurable hBase)
    (normalised_distribution_density_unit_bound hRepresentation))
  (fun x=>(f x:real_norm_metric_space hNY))).
Qed.
End CurrentLoneExtension.
