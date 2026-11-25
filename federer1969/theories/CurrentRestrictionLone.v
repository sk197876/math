(** Federer (1969), 4.1.7, p. 356:
    the original measurable restriction is exactly
    T evaluated on the characteristic-multiplied
    test through its genuine L1 extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingIsomorphism AlternatingPairing CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual MultivectorDualSealed CurrentIntegrationCriterion
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentOriginalBallFormula CurrentLoneExtension CurrentMeasurableRestriction VectorLoneCharacteristicPiece
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureLpMembershipUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed RealSubsetCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentRestrictionLone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation).
Variable A:set UT.
Hypothesis hA:measure_measurable mu A.
Local Notation s := (@CharacteristicFunction.value R UT A).
Local Notation hs := (@CharacteristicFunction.laws R UT A).

(** Source for [current_restricted_test_lone_member]:
    chi_A psi belongs to the actual original
    current L1 domain for every measurable A,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_restricted_test_lone_member psi:
  is_measure_lp_function mu 1 (partial_function_total
    (fun x:UT=>(s x*:@current_test_value R h2 n U hU m psi (set_val x):real_norm_metric_space hNY))).
Proof.
exact:(@vector_lone_characteristic_piece R UT Y NY hNY mu (distribution_representation_measure hBase)
  A s (fun x=>@current_test_value R h2 n U hU m psi (set_val x)) hs hA
  (@current_original_test_lone_member R h2 n m U hU T mu eta hRepresentation psi)).
Qed.

(** Source for [current_measurable_restriction_lone_action]:
    (T contracted A)(psi)=T(chi_A psi)
    with the right-hand side interpreted by
    the unique L1 extension, exactly Federer
    4.1.7, p. 356. *)
Theorem current_measurable_restriction_lone_action psi:
  @current_value R h2 n U hU m (@current_measurable_restriction R h2 n m U hU T hT A hA) psi=
  I (partial_function_total
    (fun x:UT=>(s x*:@current_test_value R h2 n U hU m psi (set_val x):real_norm_metric_space hNY))).
Proof.
have hNew:=@current_measurable_restriction_action R h2 n m U hU T hT A hA psi.
have hIntegral:=@current_representation_lone_total_action R h2 n m U hU T mu eta hRepresentation
  (fun x=>s x*:@current_test_value R h2 n U hU m psi (set_val x))
  (current_restricted_test_lone_member psi).
have hPoint:(fun x:UT=>@MultivectorDual.evaluation R X m (eta x)
    (s x*:@current_test_value R h2 n U hU m psi (set_val x)))=
  (fun x:UT=>s x*pairing (eta x) (@current_test_value R h2 n U hU m psi (set_val x))).
  apply:funext=>x;rewrite MultivectorDual.laws /pairing linearZ hom_scaleE;by [].
rewrite hPoint in hIntegral.
have hSubset:=(@real_subset_characteristic_integral R UT mu A s
  (fun x=>pairing (eta x) (@current_test_value R h2 n U hU m psi (set_val x))) _ hs).2 hIntegral.
exact:(congr1 (@fine R) (measure_integral_unique hNew hSubset)).
Qed.
End CurrentRestrictionLone.
