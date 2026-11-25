(** Federer (1969), 4.1.7, pp. 356–358:
    the actual L1 extension agrees with
    the original current on every compact
    test. Reuse the two original integral
    actions from 4.1.5, p. 350,
    and integral uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentDomain CurrentIntegrationCriterion CurrentOriginalBallFormula CurrentLoneExtension
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLoneOriginalAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Variable mu:set UT->\bar R.
Variable eta:UT->exterior_power X m.
Hypothesis hRepresentation:@is_normalised_current_representation R h2 n m U hU T mu eta.
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation).

(** Source for [current_lone_extension_original]: the
    original unique L1 extension has value
    T(psi) on every actual compact test,
    supporting the class-one boundary limit
    in Federer 4.1.7, p. 358. *)
Theorem current_lone_extension_original (psi:@current_test_space R h2 n U hU m):
  I (partial_function_total (fun x:UT=>(@current_test_value R h2 n U hU m psi (set_val x):
    real_norm_metric_space hNY)))=@current_value R h2 n U hU m T psi.
Proof.
have hMember:=@current_original_test_lone_member R h2 n m U hU T mu eta hRepresentation psi.
have hIntegral:=@current_representation_lone_total_action R h2 n m U hU T mu eta hRepresentation
  (fun x:UT=>@current_test_value R h2 n U hU m psi (set_val x)) hMember.
have hOriginal:=distribution_representation_action
  (normalised_distribution_representation_laws hRepresentation) psi.
exact:(congr1 (@fine R) (measure_integral_unique hIntegral hOriginal)).
Qed.
End CurrentLoneOriginalAgreement.
