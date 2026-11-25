(** Federer (1969), 4.1.7, p. 358, used in
    4.1.12, pp. 368–369: a probability Radon
    representation whose density has constant mass c
    gives current mass c. Reuse the exact original
    variation formula and the existing constant integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentSpaces CurrentDomain CurrentCoefficientNorms
  CurrentIntegrationCriterion CurrentMassSealed CurrentMassRepresentation CurrentRepresentedDensityVariation
  OpenCurrentDensityUP NormalisedCurrentSealed DistributionIntegrationRepresentationUP
  MeasureUP MeasureDensity MeasureSubsetIntegral MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  ProbabilityConstantIntegral RealSubsetIntegralGraph SummableRealFunctionUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProbabilityDensityMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := [the choiceType of set_type (U:set (real_norm_metric_space hNX))].
Variable T:@current_space R h2 n U hU m.
Variable gamma:set UT->\bar R.
Variable xi:UT->exterior_power X m.
Hypothesis hRep:@is_current_integration_representation R h2 n m U hU T gamma xi.

(** Source for [current_probability_density_mass]:
    gamma(U)=1 and mass(xi)=c give M(T)=c,
    supporting the exact masses of the segment
    series in Federer 4.1.12, pp. 368–369,
    by the original density-variation identity of
    4.1.7, p. 358. No normalisation of xi
    or positive-degree assumption is imposed. *)
Theorem current_probability_density_mass c:
  gamma setT= 1%E->(forall x,@current_vector_mass R h2 n m (xi x)=c)->
    @CurrentMass.value R h2 n m U hU T=c%:E.
Proof.
move=>hTotal hNorm.
have hT:@is_integration_representable_current R h2 n m U hU T by exists gamma,xi.
pose hGamma:=distribution_representation_measure hRep.
pose hRadon:=distribution_representation_radon hRep.
have hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi:=
  conj (distribution_representation_weak_measurable hRep) (distribution_representation_compact_norm hRep).
have hVariation:=@current_represented_original_variation R h2 n m U hU gamma hGamma hRadon xi hField T hRep hT.
have hWeight:(fun x:UT=>@current_vector_mass R h2 n m (xi x))=(fun _=>c).
  apply:funext=>x;exact:hNorm.
rewrite (@current_represented_mass_total R h2 n m U hU T hT) hVariation hWeight
  (measure_with_density_laws gamma (real_total_integrand (fun _:UT=>c)) setT)
  /measure_subset_upper_integral.
have hConstant:is_measure_integral gamma (real_total_integrand (fun _:UT=>c)) c%:E.
  apply:(@measure_integral_graph_equivalent R UT gamma _ _ c%:E _
    (@probability_constant_integral R UT gamma hGamma c hTotal))=>x z.
  change (c%:E=z<->partial_function_graph (real_total_integrand (fun _:UT=>c)) x z).
  by rewrite real_total_integrand_graph.
have hSubset:=(@real_subset_integral_total R UT gamma setT (fun _=>c) (fun _=>c) c%:E
  (fun _ _=>erefl) (fun _ hFalse=>False_ind _ (hFalse Logic.I))).2 hConstant.
exact:(@measure_upper_integral_unique R UT gamma _ _ _
  (measure_upper_integral_specification _ _) hSubset.2.1).
Qed.
End CurrentProbabilityDensityMass.
