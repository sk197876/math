(** Federer (1969), 4.1.5, p. 350:
    the original variation Radon measure integrates
    every positive compact scalar test. Reuse the
    existing sealed integral functional of 2.5.1;
    no extra integrability premise is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ContinuousDualUP WeakEvaluationTopologyUP
  FunctionLatticeUP CompactSupportFunctionUP SummableRealFunctionUP RealIntegralFunctionalUP
  RealIntegralFunctionalSealed NormalisedDistributionRepresentationUP NormalisedDistributionScalarIntegral
  MeasureIntegralUP MeasureIntegralUniqueness DistributionVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalisedScalarIntegralGauge.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.
Variable mu:set X->\bar R.
Variable k:X->D.
Hypothesis hRepresentation:is_normalised_distribution_representation hD hO value S mu k.
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R X)).

Local Notation F := (@normalised_distribution_scalar_integral R X Y NY hNY D ed DN hD O hO
  E value S mu k hRepresentation).

(** Source for [normalised_scalar_integral_original_gauge]: the
    original ||S|| equals its actual compact
    scalar integral, Federer 4.1.5, p. 350,
    independently of any choice of integral values. *)
Theorem normalised_scalar_integral_original_gauge f:
  Kplus f ->is_distribution_variation_value NY value S f (F f)%:E.
Proof.
move=>hf.
have[b [hGauge hIntegral]]:=normalised_distribution_original_gauge hRepresentation hf.
have hActual:=@normalised_distribution_scalar_integral_laws R X Y NY hNY D ed DN hD O hO
  E value S mu k hRepresentation f hf.
have hEqual:=measure_integral_unique hActual hIntegral.
have hValue:F f=b by injection hEqual.
by rewrite hValue.
Qed.
End NormalisedScalarIntegralGauge.
