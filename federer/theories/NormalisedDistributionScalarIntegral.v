(** Federer (1969), 4.1.5, p. 350:
    the original variation Radon measure integrates
    every positive compact scalar test. Reuse the
    existing sealed integral functional of 2.5.1;
    no extra integrability premise is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ContinuousDualUP WeakEvaluationTopologyUP
  FunctionLatticeUP CompactSupportFunctionUP SummableRealFunctionUP RealIntegralFunctionalUP
  RealIntegralFunctionalSealed NormalisedDistributionRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalisedDistributionScalarIntegral.
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

(** Source for [normalised_distribution_positive_summability]:
    the original finite variation integrates K(U)+,
    Federer 4.1.5, p. 350. *)
Lemma normalised_distribution_positive_summability:Kplus `<=` summable_real_functions mu.
Proof.
move=>f hf.
have[b [_ hB]]:=normalised_distribution_original_gauge hRepresentation hf.
by exists b.
Qed.

(** Source for [normalised_distribution_scalar_integral]: the
    original positive compact scalar integral,
    Federer 4.1.5, p. 350, through
    the already proved opaque integral of 2.5.1. *)
Definition normalised_distribution_scalar_integral:(X->R)->R:=
  @RealIntegralFunctional.value R X mu Kplus normalised_distribution_positive_summability.

(** Source for [normalised_distribution_scalar_integral_laws]:
    finite compact scalar integrability for the
    actual L1 density theorem of Federer
    4.1.5, p. 350. *)
Lemma normalised_distribution_scalar_integral_laws:
  is_real_integral_functional mu Kplus normalised_distribution_scalar_integral.
Proof. exact:(@RealIntegralFunctional.laws R X mu Kplus normalised_distribution_positive_summability). Qed.
End NormalisedDistributionScalarIntegral.
