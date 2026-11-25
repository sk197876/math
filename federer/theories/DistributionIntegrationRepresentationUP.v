(** Federer (1969), 4.1.5, pp. 349–350:
    representation by integration on the original
    domain. These independent laws use an abstract
    continuous dual and its original weak topology.
    Existence and normalization are separate theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ContinuousDualUP WeakEvaluationTopologyUP OpenFamilyTopologyMathcomp
  PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP MeasureSubsetIntegral
  SummableRealFunctionUP DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_distribution_integration_representation]:
    the Radon measure rho, weakly measurable original
    Y* field xi, finite compact norm integrals and
    original test action in Federer 4.1.5, p. 349.
    The dual is specified by its public evaluation
    and least-norm laws, not by a chosen carrier. *)
Record is_distribution_integration_representation (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (E:lmodType R) (value:E->X->Y) (S:Hom E R^o)
    (rho:set X->\bar R) (xi:X->D):Prop:={
  (** Source for [distribution_representation_measure]:
      rho is an actual measure, Federer 4.1.5,
      p. 349. *)
  distribution_representation_measure:is_measure rho;
  (** Source for [distribution_representation_radon]:
      rho is Radon on the original domain,
      Federer 4.1.5, p. 349. *)
  distribution_representation_radon:is_radon_measure rho;
  (** Source for [distribution_representation_weak_measurable]:
      the actual original weak Y* field is measurable,
      Federer 4.1.5, p. 349. *)
  distribution_representation_weak_measurable:is_measure_measurable_function rho
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1)));
  (** Source for [distribution_representation_compact_norm]:
      the original dual norm has a finite integral
      on every compact set, Federer 4.1.5, p. 349. *)
  distribution_representation_compact_norm:forall K:set X,compact K ->exists c:R,
    is_measure_subset_integral rho K (real_total_integrand (fun x=>DN (xi x))) c%:E;
  (** Source for [distribution_representation_action]:
      every original S(phi) equals its pairing integral,
      Federer 4.1.5, p. 349. *)
  distribution_representation_action:is_distribution_integral_action rho ed xi value S
}.
