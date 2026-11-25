(** Federer (1969), 4.1.7, pp. 356, 359:
    contraction with the characteristic zero-form
    is the original measurable restriction. This
    identifies the actual opaque current operations
    through their original test integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import CurrentEvaluation Hom TensorUP ScalarCoefficients RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingIsomorphism AlternatingZero AlternatingProduct AlternatingPairing
  ZeroFormScalarProduct CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentMeasurableMultiplierUP CurrentMeasurableProducts CurrentMeasurableRestriction
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness
  MeasureSubsetIntegral SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed RealSubsetCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCharacteristicContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Variable A:set UT.
Hypothesis hA:measure_measurable mu A.
Local Notation chi := (@CharacteristicFunction.value R UT A).
Local Notation hChi := (@CharacteristicFunction.laws R UT A).
Variable phi:UT->A_m X R^o 0.
Hypothesis hPhi:is_locally_summable_current_field (@current_form_comass_real_norm R h2 n 0%N) mu phi.
Hypothesis hValues:forall x,phi x=@zero_form R X R^o (chi x).

(** Source for [current_characteristic_contraction_restriction]:
    T contracted with the original characteristic
    zero-form equals T restricted to A,
    supporting Federer 4.1.7, pp. 356, 359.
    The restricting set may have infinite measure. *)
Theorem current_characteristic_contraction_restriction:
  @current_measurable_contraction R h2 n 0%N m U hU T hT phi hPhi=
    @current_measurable_restriction R h2 n m U hU T hT A hA.
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>psi.
have hContraction:=@current_measurable_contraction_action R h2 n 0%N m U hU T hT phi hPhi psi.
have hPoint:(fun x:UT=>pairing (xi x) (form_wedge h2 (scalar_bilinear R) (phi x)
    (@current_test_value R h2 n U hU m psi (set_val x))))=
  (fun x=>chi x*pairing (xi x) (@current_test_value R h2 n U hU m psi (set_val x))).
  apply:funext=>x.
  by rewrite (hValues x) original_zero_form_wedge_scalar /pairing linearZ hom_scaleE.
rewrite hPoint in hContraction.
have hRestriction:=@current_measurable_restriction_action R h2 n m U hU T hT A hA psi.
have hIntegral:=(@real_subset_characteristic_integral R UT mu A chi
  (fun x=>pairing (xi x) (@current_test_value R h2 n U hU m psi (set_val x)))
  (@current_value R h2 n U hU m (@current_measurable_restriction R h2 n m U hU T hT A hA) psi)%:E
  hChi).1 hRestriction.
exact:(EFin_inj (measure_integral_unique hContraction hIntegral)).
Qed.
End CurrentCharacteristicContraction.
