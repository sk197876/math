(** Federer (1969), 4.1.7, p. 356:
    the original restriction T contracted A
    for every ||T||-measurable A. The value
    is the opaque measurable scalar multiplier;
    its public action is the literal subset
    integral with the original variation density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  NormBoundedBilinearUP WhitneyExtensionFunction ContinuousMultilinearBilinearLift LocalUniquenessExample
  CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierSealed CharacteristicRadonLocalIntegral
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed RealSubsetCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentMeasurableRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Z := (exterior_power X m).
Local Notation NZ := (@current_vector_mass R h2 n m).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation C := (@current_space R h2 n U hU m).

(** Source for [current_density_scalar_multiplication_bounded]:
    scalar multiplication has the original bound
    one in mass, supporting the measurable
    restriction in Federer 4.1.7, p. 356.
    Reuse the earlier scalar bilinear law. *)
Lemma current_density_scalar_multiplication_bounded:
  norm_bounded_bilinear NZ (fun a:R^o=>`|a|) NZ (fun z (a:R^o)=>a*:z).
Proof.
exact:(norm_bounded_bilinear_flip (@scalar_vector_bounded_bilinear R Z NZ hNZ)).
Qed.
Variable T:C.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Variable A:set UT.
Hypothesis hA:measure_measurable mu A.
Local Notation s := (@CharacteristicFunction.value R UT A).
Local Notation hs := (@CharacteristicFunction.laws R UT A).
Local Notation hField := (@characteristic_radon_locally_summable R UT mu
  (distribution_representation_measure hBase) (distribution_representation_radon hBase) A s hs hA).

(** Source for [current_measurable_restriction]: the
    original T contracted A for every
    variation-measurable A, Federer 4.1.7,
    p. 356. A is a set in U. *)
Definition current_measurable_restriction:C:=
  @CurrentMeasurableMultiplier.value R h2 n m m U hU R^o (fun a:R^o=>`|a|)
    (@scalar_absolute_value_norm R) (@scalar_norm_separable R)
    (fun z a=>a*:z) current_density_scalar_multiplication_bounded T hT s hField.

(** Source for [current_measurable_restriction_representable]:
    restriction preserves integration representability,
    supporting the original definition in Federer
    4.1.7, p. 356. *)
Lemma current_measurable_restriction_representable:
  @is_integration_representable_current R h2 n m U hU current_measurable_restriction.
Proof.
exact:(@CurrentMeasurableMultiplier.laws R h2 n m m U hU R^o (fun a:R^o=>`|a|)
  (@scalar_absolute_value_norm R) (@scalar_norm_separable R)
  (fun z a=>a*:z) current_density_scalar_multiplication_bounded T hT s hField).2.
Qed.

(** Source for [current_measurable_restriction_action]:
    (T contracted A)(psi) is the original
    integral over A of <eta,psi>, Federer
    4.1.7, p. 356, through 4.1.5.
    The set A may have infinite variation. *)
Theorem current_measurable_restriction_action psi:
  is_measure_subset_integral mu A (real_total_integrand
    (fun x:UT=>pairing (eta x) (@current_test_value R h2 n U hU m psi (set_val x))))
    (@current_value R h2 n U hU m current_measurable_restriction psi)%:E.
Proof.
have h:=(@CurrentMeasurableMultiplier.laws R h2 n m m U hU R^o (fun a:R^o=>`|a|)
  (@scalar_absolute_value_norm R) (@scalar_norm_separable R)
  (fun z a=>a*:z) current_density_scalar_multiplication_bounded T hT s hField).1 psi.
have hPoint:(fun x:UT=>pairing (s x*:eta x) (@current_test_value R h2 n U hU m psi (set_val x)))=
  (fun x:UT=>s x*pairing (eta x) (@current_test_value R h2 n U hU m psi (set_val x))).
  apply:funext=>x;by rewrite /pairing linearZ.
rewrite hPoint in h.
exact:(@real_subset_characteristic_integral R UT mu A s
  (fun x:UT=>pairing (eta x) (@current_test_value R h2 n U hU m psi (set_val x)))
  (@current_value R h2 n U hU m current_measurable_restriction psi)%:E hs).2 h.
Qed.
End CurrentMeasurableRestriction.
