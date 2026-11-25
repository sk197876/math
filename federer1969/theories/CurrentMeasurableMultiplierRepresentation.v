(** Federer (1969), 4.1.8, p. 362: use the
    original measurable product as an actual density
    representation. All measure and local-integrability
    laws are the already proved 4.1.7 laws;
    only their public representation assembly is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import AlternatingPairing Hom TensorUP RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentDomain
  CurrentCoefficientNorms CurrentVectorSpaces CurrentSpaces CurrentEvaluation CurrentIntegrationCriterion
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentDensityNormMeasurable CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierExistence CurrentMeasurableMultiplierSealed UnitBilinearLocalIntegral
  MeasurableBoundedBilinearProduct NormBoundedBilinearUP VectorDaniellHypotheses FiniteNormMetricPolish
  OpenCurrentDensityUP OpenCurrentDensitySealed MultivectorDualSealed
  PartialFunctionUP PartialFunctionBasic MeasureUP RadonMeasureUP RadonBorelRegularity MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentMeasurableMultiplierRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q p:nat.
Local Notation X := (R_n R n).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation NZ := (fun m=>@current_vector_mass R h2 n m).
Local Notation hNZ := (fun m=>@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable V:lmodType R.
Variable NV:V->R.
Hypothesis hNV:is_real_norm NV.
Hypothesis hSepV:is_separable_normed_space hNV.
Variable F:Z q->V->Z p.
Hypothesis hF:norm_bounded_bilinear (NZ q) NV (NZ p) F.
Variable T:@current_space R h2 n U hU q.
Hypothesis hT:@is_integration_representable_current R h2 n q U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n q U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n q U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n q U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation hm := (distribution_representation_measure hBase).
Local Notation hr := (distribution_representation_radon hBase).
Variable f:UT->V.
Hypothesis hField:is_locally_summable_current_field hNV mu f.

Local Notation S := (@CurrentMeasurableMultiplier.value R h2 n q p U hU V NV hNV hSepV F hF T hT f hField).
Local Notation xi := (fun x=>F (eta x) (f x)).

(** Source for [current_measurable_multiplier_representation]: the
    actual original measurable product has density
    F(vec T,f) against the original variation of
    T, supporting Federer 4.1.8, p. 362, by
    4.1.7, pp. 355–356. All original local
    summability hypotheses remain unchanged. *)
Theorem current_measurable_multiplier_representation:
  @is_current_integration_representation R h2 n p U hU S mu xi.
Proof.
have hData:=@current_measurable_multiplier_density_integrable R h2 n q p U hU V NV hNV hSepV
  F hF T hT f hField.
constructor.
- exact:hm.
- exact:hr.
- exact:hData.1.
- exact:hData.2.
- move=>psi.
  have hAction:=(@CurrentMeasurableMultiplier.laws R h2 n q p U hU V NV hNV hSepV
    F hF T hT f hField).1 psi.
  apply:(measure_integral_graph_equivalent _ hAction)=>x z.
  change (partial_function_graph (real_total_integrand (fun x=>pairing (xi x)
      (@current_test_value R h2 n U hU p psi (set_val x)))) x z <->
    partial_function_graph (real_total_integrand (fun x=>@MultivectorDual.evaluation R X p (xi x)
      (@current_test_value R h2 n U hU p psi (set_val x)))) x z).
  by rewrite !real_total_integrand_graph MultivectorDual.laws.
Qed.
End CurrentMeasurableMultiplierRepresentation.
