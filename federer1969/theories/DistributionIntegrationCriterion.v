(** Federer (1969), 4.1.5, p. 349:
    the original finite-gauge condition is necessary
    and sufficient for representation by a Radon
    measure and a weak dual density whose norm
    is integrable on every original compact set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP ContinuousDualUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness VectorDaniellHypotheses
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation WeakEvaluationTopologyUP
  DistributionVariationDomain DistributionFiniteVariationUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP FiniteDistributionRadonRepresentation DistributionRepresentationFiniteGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionIntegrationCriterion.
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

(** Source for [distribution_integration_criterion]:
    the original necessary and sufficient criterion
    of Federer 4.1.5, p. 349, with the actual
    original domain, compact tests and abstract Y*.
    The converse permits arbitrary unnormalized densities. *)
Theorem distribution_integration_criterion:
  @is_finite_distribution_variation R XT U Y NY DT values S <->
  exists rho:set UT->\bar R,exists xi:UT->D,
    is_distribution_integration_representation hD hO dvalues S rho xi.
Proof.
split.
- move=>hFinite.
  have[rho [xi hRepresentation]]:=@finite_distribution_radon_representation R n Y NY hNY hY hSeparable
    U hU E ev hE S D ed DN hD O hO hFinite.
  exists rho,xi; exact:normalised_distribution_representation_laws hRepresentation.
- move=>[rho [xi hRepresentation]].
  exact:(@distribution_representation_finite_gauge R UT Y NY hNY D ed DN hD O hO DT dvalues S rho xi
    hRepresentation).
Qed.
End DistributionIntegrationCriterion.
