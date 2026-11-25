(** Federer (1969), 4.1.21, p. 378: keep the
    exact original variation when restricting a current
    to a compact null subset. Derive the restriction formula
    from 4.1.7's all-set density variation and the
    original almost-everywhere unit density. No finite
    mass or null-boundary assumption enters this adapter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual
  MultivectorDualSealed NormalisedCurrentSealed OpenCurrentDensityUP
  CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierSealed
  CurrentMeasurableMultiplierRepresentation CurrentMeasurableRestriction
  CurrentRepresentedDensityVariation CurrentMassSealed CurrentMassRepresentation
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  NormBoundedBilinearUP WhitneyExtensionFunction ContinuousMultilinearBilinearLift
  LocalUniquenessExample CharacteristicRadonLocalIntegral
  CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureDensityUP MeasureDensity MeasureDensityTransfer RegularCharacteristicDensity
  RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentMeasurableRestrictionVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT:=(current_domain R n U).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Z:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Variable T:C.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta:=(@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hOriginal:=(@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hBase:=(normalised_distribution_representation_laws hOriginal).
Local Notation hm:=(distribution_representation_measure hBase).
Local Notation hr:=(distribution_representation_radon hBase).
Variable A:set UT.
Hypothesis hA:measure_measurable mu A.
Local Notation chi:=(@CharacteristicFunction.value R UT A).
Local Notation hChi:=(@CharacteristicFunction.laws R UT A).
Local Notation S:=(@current_measurable_restriction R h2 n m U hU T hT A hA).

(** Source for [current_measurable_restriction_density_representation]:
    the original restriction has density chi_A times the
    original normalized density, with the same original
    measure, by 4.1.7, p. 356. This supporting
    representation is derived, not an extra premise on
    the compact restriction in 4.1.21, p. 378. *)
Theorem current_measurable_restriction_density_representation:
  @is_current_integration_representation R h2 n m U hU S mu
    (fun x=>chi x*:eta x).
Proof.
pose hField:=@characteristic_radon_locally_summable R UT mu hm hr A chi hChi hA.
exact:(@current_measurable_multiplier_representation R h2 n m m
  U hU R^o (fun a:R^o=>`|a|) (@scalar_absolute_value_norm R)
  (@scalar_norm_separable R) (fun z (a:R^o)=>a*:z)
  (@current_density_scalar_multiplication_bounded R h2 n m)
  T hT chi hField).
Qed.

(** Source for [current_measurable_restriction_variation]:
    the literal original variation of T restricted to A
    is ||T|| restricted to A on every set, from
    the exact density formula of 4.1.7, p. 358,
    supporting the null-set corollary of 4.1.21, p. 378.
    A is only variation-measurable, and every representation
    witness for the restricted current is retained. *)
Theorem current_measurable_restriction_variation
    (hS:@is_integration_representable_current R h2 n m U hU S):
  @NormalisedCurrent.measure R h2 n m U hU S hS=measure_restrict mu A.
Proof.
pose xi:=fun x:UT=>chi x*:eta x.
have hRep:=current_measurable_restriction_density_representation.
have hField:@is_locally_integrable_open_current_density R h2 n m U mu xi.
  exact:conj (distribution_representation_weak_measurable hRep)
    (distribution_representation_compact_norm hRep).
pose nu:=@NormalisedCurrent.measure R h2 n m U hU S hS.
have hVariation:=@current_represented_original_variation R h2 n m U hU
  mu hm hr xi hField S hRep hS.
have hDensity:is_measure_density mu (real_total_integrand (fun x=>VN (xi x))) nu.
  rewrite /nu hVariation;exact:measure_with_density_laws.
have hEqual:measure_almost_equal mu
    (real_total_integrand (fun x=>VN (xi x))) (real_total_integrand chi).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _
    (normalised_distribution_density_unit_norm hOriginal))=>x hx.
  have hMass:VN (xi x)=chi x.
    rewrite /xi (real_seminorm_scale hVN.1) hx mulr1.
    case:(pselect (A x))=>hInside.
    - by rewrite (characteristic_on_set hChi hInside) normr1.
    - by rewrite (characteristic_off_set hChi hInside) normr0.
  exists (chi x)%:E;split;rewrite real_total_integrand_graph=>//.
  by rewrite hMass.
have hRestrictedDensity:=@measure_density_almost_equal R UT mu nu hm
  (real_total_integrand (fun x=>VN (xi x))) (real_total_integrand chi)
  hDensity hEqual.
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm hr).
have hCanonical:=@regular_characteristic_density R UT mu hm hRegular A chi hChi.
apply:funext=>B.
exact:(@measure_density_unique R UT mu (real_total_integrand chi)
  nu (measure_restrict mu A) hRestrictedDensity hCanonical B).
Qed.

(** Source for [current_measurable_restriction_mass]: the
    mass of the original measurable restriction is exactly
    ||T||(A), including infinite values, from 4.1.7,
    p. 358, for the compact-null reduction of 4.1.21,
    p. 378. Neither compactness nor finite M(T) is
    added to this supporting equality. *)
Theorem current_measurable_restriction_mass:
  @CurrentMass.value R h2 n m U hU S=mu A.
Proof.
pose hS:=@current_measurable_restriction_representable R h2 n m U hU T hT A hA.
rewrite (@current_represented_mass_total R h2 n m U hU S hS)
  (@current_measurable_restriction_variation hS).
change (mu (A `&` setT)=mu A).
congr mu;apply/seteqP;split;first by move=>x [hx _].
by move=>x hx;split.
Qed.
End CurrentMeasurableRestrictionVariation.
