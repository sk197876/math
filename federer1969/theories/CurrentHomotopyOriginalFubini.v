(** Federer (1969), 4.1.9, pp. 363–364: the
    original product-variation integral equals the literal
    time integral of its actual spatial section integrals.
    Reuse the preceding product Fubini theorem and the
    exact unit-segment variation, retaining all partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianRadonFubini
  NormalisedCurrentSealed CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity
  CurrentHomotopyTimePartialIntegral DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionPrecomposition PartialProductSections ParameterizedIntegral
  MeasureIntegralUP MeasureSubsetIntegral RealMetricBackground LebesgueScalarMeasure ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyOriginalFubini.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation S := (@current_homotopy_time_segment R A hA h2).
Local Notation hS := (@current_homotopy_time_representable R h2 A hA).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation CT := (current_domain R (1+n)%N (@euclidean_cartesian_set R 1%N n AT U)).
Local Notation J := (@CartesianCurrentDomain.join R 1%N n AT U).
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N AT hAT S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j U hU T hT).
Local Notation hNS := (@NormalisedCurrent.laws R h2 1%N 1%N AT hAT S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j U hU T hT).
Local Notation baseS := (normalised_distribution_representation_laws hNS).
Local Notation baseT := (normalised_distribution_representation_laws hNT).
Local Notation hAlpha := (distribution_representation_measure baseS).
Local Notation hBeta := (distribution_representation_measure baseT).
Local Notation lambda := (@CartesianCurrentMeasure.value R 1%N n AT U alpha beta hAlpha hBeta).

(** Source for [current_homotopy_original_fubini]: every
    original product integral becomes the printed [0,1]
    time integral of its actual spatial integrals,
    supporting Federer 4.1.9, pp. 363–364. Neither
    finite total mass nor totality of inner integrals
    is imposed; their original partial graphs are retained. *)
Theorem current_homotopy_original_fubini
    (f:partial_function CT (extended_real_line R)) a:
  is_measure_integral lambda f a->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
    (@current_homotopy_scalar_time_integrand R A
      (parameterized_integral beta (partial_product_vertical_section (partial_function_precompose J f)))) a.
Proof.
move=>hIntegral.
have hFactors:=@current_cartesian_radon_vertical_fubini R 1%N n AT U hAT hU alpha beta hAlpha hBeta
  (distribution_representation_radon baseS) (distribution_representation_radon baseT) f a hIntegral.
exact:(@current_homotopy_time_partial_integral_iff R h2 A hA _ a).1 hFactors.
Qed.
End CurrentHomotopyOriginalFubini.
