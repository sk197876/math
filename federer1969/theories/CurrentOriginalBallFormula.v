(** Federer (1969), 4.1.7, p. 357: the
    original characteristic-ball quotients of an
    integration-representable current. The numerator
    is its actual L1 extension from 4.1.5,
    p. 350. One conull set works for every covector. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentSpaces MultivectorDualSealed CurrentMultivectorDual
  DistributionVariationDomain DistributionFiniteVariationUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP DistributionIntegrationCriterion FiniteDistributionRadonRepresentation CurrentIntegrationCriterion
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureLpMembershipUP MeasureAlmostUP
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed
  DualLoneIntegralUP DualLoneIntegralSealed DistributionOriginalBallFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentOriginalBallFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation D := (exterior_power X m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation UT := (metric_subset (U:set XT)).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).


Variable T:C.
Variable mu:set UT->\bar R.
Variable k:UT->D.
Hypothesis hRepresentation:@is_normalised_current_representation R h2 n m U hU T mu k.
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hK:=distribution_representation_weak_measurable hBase.
Let hUnit:=normalised_distribution_density_unit_bound hRepresentation.

(** Source for [current_representation_lone_integral]:
    the unique original L1 extension used in the
    orienting-field quotients of Federer 4.1.7,
    p. 357. Its partial-domain laws come from
    the actual dual integral of 4.1.5. *)
Definition current_representation_lone_integral:=
  @DualLoneIntegral.value R UT Y NY hNY (@current_form_separable R h2 n m)
    D ed DN hDual O hO mu hm k hK hUnit.

(** Source for [current_original_ball_formula]: the
    exact original current quotient converges to the
    actual mass-one multivector density, simultaneously
    for all covectors, Federer 4.1.7, p. 357.
    This is the conull-set assertion; the maximal
    domain of the original orienting field is separate. *)
Theorem current_original_ball_formula:
  measure_almost_everywhere mu [set x:UT|forall y:Y,forall eta:R,0<eta ->
    exists d:R,0<d /\forall r:R,0<r ->r<d ->
      exists mass:R,mu (metric_closed_ball x r)=mass%:E /\0<mass /\
        is_measure_lp_function mu 1 (partial_function_total
          (fun z=>((@CharacteristicFunction.value R UT (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY))) /\
        `|current_representation_lone_integral (partial_function_total
          (fun z=>((@CharacteristicFunction.value R UT (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY)))/mass-ed (k x) y|<eta].
Proof.
exact:(@distribution_original_ball_formula R n Y NY hNY
  (@current_form_separable R h2 n m) U hU E ev hE (action T) D ed DN hDual O hO mu k hRepresentation).
Qed.
End CurrentOriginalBallFormula.
