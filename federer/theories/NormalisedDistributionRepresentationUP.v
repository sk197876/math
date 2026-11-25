(** Federer (1969), 4.1.5, p. 350:
    the original variation Radon measure represents
    the distribution with an almost-everywhere unit
    dual density. The independent specification also
    retains the literal K(U)+ gauge identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ContinuousDualUP WeakEvaluationTopologyUP
  PartialFunctionBasic MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP
  FunctionLatticeUP CompactSupportFunctionUP DistributionVariationUP DistributionIntegrationRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_normalised_distribution_representation]:
    the normalized original integral representation in
    Federer 4.1.5, p. 350. The Radon measure
    represents the original scalar-test gauge, and no
    Borel variation measure is assigned outside this case. *)
Record is_normalised_distribution_representation (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (E:lmodType R) (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o)
    (rho:set X->\bar R) (k:X->D):Prop:={
  (** Source for [normalised_distribution_representation_laws]:
      the original Radon representation and compact
      norm integrability, Federer 4.1.5, pp. 349–350. *)
  normalised_distribution_representation_laws:
    is_distribution_integration_representation hD hO value S rho k;
  (** Source for [normalised_distribution_density_unit_norm]:
      ||k(x)||=1 almost everywhere, Federer 4.1.5,
      p. 350. *)
  normalised_distribution_density_unit_norm:
    measure_almost_everywhere rho [set x|DN (k x)= 1];
  (** Source for [normalised_distribution_density_norm_measurable]:
      the original dual norm is measurable, from
      2.5.12 as applied in Federer 4.1.5, p. 350. *)
  normalised_distribution_density_norm_measurable:
    is_measure_measurable_function rho (real_total_integrand (fun x=>DN (k x)));
  (** Source for [normalised_distribution_density_unit_bound]:
      the representative lies in the original closed
      unit dual ball, from 2.5.12 as used in
      Federer 4.1.5, p. 350. *)
  normalised_distribution_density_unit_bound:forall x,DN (k x)<= 1;
  (** Source for [normalised_distribution_original_gauge]:
      the Radon measure represents the literal
      original ||S|| on K(U)+, Federer 4.1.5,
      p. 350. *)
  normalised_distribution_original_gauge:forall f,
    positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    exists b:R,is_distribution_variation_value NY value S f b%:E /\
      is_measure_integral rho (real_total_integrand f) b%:E
}.
