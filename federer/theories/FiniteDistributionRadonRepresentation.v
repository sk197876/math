(** Federer (1969), 4.1.5, pp. 349–350:
    the original finite-gauge condition produces the
    actual Radon variation measure and normalized weak
    density in the abstract continuous dual Y*.
    All compact continuous extension and representation
    hypotheses have been proved, and the literal
    original K(U)+ gauge is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP ContinuousDualUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  VectorDaniellHypotheses VectorDaniellRepresentationUP VectorDaniellNormalisationUP
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation WeakEvaluationTopologyUP
  DistributionVariationDomain DistributionFiniteVariationUP DistributionContinuousExtensionSealed
  DistributionSubspaceExtension DistributionSubspaceVariation DistributionRadonExtension DistributionOriginalRadonFormula
  WeakDualRealisationUP WeakDualRealisationSealed WeakDualRealisationMeasurable WeakDualDensityNormTransport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP DistributionIntegralFieldUP
  MeasureUP RadonMeasureUP RealIntegralFunctionalUP SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteDistributionRadonRepresentation.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSeparable:is_separable_normed_space hNY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Variable S:Hom DT R^o.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.

(** Source for [finite_distribution_radon_representation]:
    sufficiency of the original finite-gauge criterion
    and the normalized original Radon representation,
    Federer 4.1.5, pp. 349–350. The actual
    original tests and abstract continuous dual are used. *)
Theorem finite_distribution_radon_representation:
  @is_finite_distribution_variation R XT U Y NY DT values S ->
  exists rho:set UT->\bar R,exists k:UT->D,
    is_normalised_distribution_representation hD hO dvalues S rho k.
Proof.
move=>hFinite.
pose T:=@DistributionContinuousExtension.value R n Y NY hNY hY U hU E ev hE S hFinite.
have hT:=@DistributionContinuousExtension.laws R n Y NY hNY hY U hU E ev hE S hFinite.
pose Q:=@CompactContinuousVectorFields.compact_continuous_vector_fields R UT Y NY hNY.
pose TU:=@distribution_subspace_extension R XT U Y T.
have[rho [k [hm [hr [hIntegral hk]]]]]:=@distribution_radon_extension_representation
  R n Y NY hNY hY hSeparable U hU E ev hE S hFinite T hT.
pose J:=@WeakDualRealisation.value R Y NY hNY D ed DN hD.
have hJ:=@WeakDualRealisation.laws R Y NY hNY D ed DN hD.
pose xi:=fun x:UT=>J (k x).
have hRepresentation:@is_distribution_integration_representation R UT Y NY hNY D ed DN hD O hO
    DT dvalues S rho xi.
  constructor=>//.
  - exact:(@weak_dual_realisation_measurable R UT Y NY hNY D ed DN J hJ O hO rho hm k
      (vector_daniell_density_measurable (normalised_vector_density_laws hk))).
  - exact:(@weak_dual_density_compact_norm R UT Y NY hNY D ed DN J hJ rho hm Q TU k hk hr).
  - move=>psi.
    have hFormula:=@distribution_original_radon_formula R X Y N NY hN hNY U E ev hE S T rho k
      hT (normalised_vector_density_laws hk) psi.
    have hEq:(fun x:UT=>ed (xi x) (dvalues psi x))=
        (fun x:UT=>val (k x) (smooth_test_value hE psi (set_val x))).
      apply:funext=>x; exact:(@weak_dual_realisation_evaluation R Y NY hNY D ed DN J hJ (k x)
        (smooth_test_value hE psi (set_val x))).
    rewrite /is_distribution_integral_action hEq; exact hFormula.
exists rho,xi; constructor.
- exact hRepresentation.
- exact:(@weak_dual_density_unit_norm R UT Y NY hNY D ed DN J hJ rho hm Q TU k hk).
- exact:(@weak_dual_density_norm_measurable R UT Y NY hNY D ed DN J hJ rho Q TU k hk).
- exact:(@weak_dual_density_unit_bound R UT Y NY hNY D ed DN J hJ rho Q TU k hk).
- move=>f hf; exists (variation_integral NY Q TU f); split.
  + exact:(@distribution_original_gauge_variation_value R n Y NY hNY hY U hU E ev hE S hFinite T hT f hf).
  + exact:hIntegral f hf.
Qed.
End FiniteDistributionRadonRepresentation.
