(** Federer (1969), 4.1.5, p. 350:
    weak convergence in the actual distribution
    space gives both printed lower-limit
    inequalities. Scalar gauges retain arbitrary
    infinite values; open-set masses use the
    original normalized Radon representations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  ContinuousMultilinearSealed ContinuousRealDual OpenFamilyConvergence WeakEvaluationTopologySealed
  WeakSequenceEvaluationLimit SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothTestTopology FunctionLatticeUP CompactSupportFunctionUP DistributionVariationDomain
  DistributionVariationSealed DistributionVariationLowerLimit ExtendedLowerLimit
  ContinuousDualUP WeakEvaluationTopologyUP DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  NormalisedDistributionScalarIntegral NormalisedScalarIntegralGauge RealIntegralFunctionalUP
  OriginalGaugeRadonOpenLowerLimit SubtypeCompactHausdorff OpenSubspaceMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionWeakLowerSemicontinuity.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Variable D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y N NY hN hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation WO := (@continuous_real_dual_weak_opens R DT SO hSO).
Variable S:nat->DD.
Variable T:DD.
Hypothesis hWeak:open_family_converges WO (S @ \oo) T.
Let hPoint:=@weak_sequence_real_evaluations_limit R DT DD (fun a phi=>eD a phi) WO
  (@WeakEvaluationTopology.convergence R DT DD (fun a phi=>eD a phi)) S T hWeak.

(** Source for [distribution_weak_scalar_variation_lower_limit]:
    the first original weak lower-semicontinuity
    inequality in Federer 4.1.5, p. 350,
    for every positive compact scalar test,
    without any integration-representation premise. *)
Theorem distribution_weak_scalar_variation_lower_limit (f:UT->R)
    (hf:positive_function_lattice (@compactly_supported_continuous_functions R UT) f):
  (@DistributionVariation.value R UT Y NY hNY DT dvalues (eD T) f hf.2<=
    extended_lower_limit (fun i=>@DistributionVariation.value R UT Y NY hNY DT dvalues (eD (S i)) f hf.2))%E.
Proof.
exact:(@distribution_variation_lower_limit R UT Y NY DT dvalues (fun i=>eD (S i)) (eD T) f
  (fun i=>@DistributionVariation.value R UT Y NY hNY DT dvalues (eD (S i)) f hf.2)
  (@DistributionVariation.value R UT Y NY hNY DT dvalues (eD T) f hf.2)
  (fun i=>@DistributionVariation.laws R UT Y NY hNY DT dvalues (eD (S i)) f hf.2)
  (@DistributionVariation.laws R UT Y NY hNY DT dvalues (eD T) f hf.2) hPoint).
Qed.

Variable YD:lmodType R.
Variable edY:Hom YD (Hom Y R^o).
Variable DNY:YD->R.
Hypothesis hYD:is_continuous_dual hNY edY DNY.
Variable OY:set (set YD).
Hypothesis hOY:is_weak_evaluation_topology (fun a y=>edY a y) OY.
Variable rho:nat->set UT->\bar R.
Variable k:nat->UT->YD.
Hypothesis hNorm:forall i,is_normalised_distribution_representation hYD hOY dvalues (eD (S i)) (rho i) (k i).
Variable nu:set UT->\bar R.
Variable xi:UT->YD.
Hypothesis hNormT:is_normalised_distribution_representation hYD hOY dvalues (eD T) nu xi.

(** Source for [distribution_weak_open_variation_lower_limit]:
    the second original weak lower-semicontinuity
    inequality in Federer 4.1.5, p. 350,
    for every open subset of U. The
    measures are the original Radon variations;
    infinite masses are retained. *)
Theorem distribution_weak_open_variation_lower_limit:
  forall V:set UT,open V ->(nu V<=extended_lower_limit (fun i=>rho i V))%E.
Proof.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hLocal:=@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN.
have hULocal:=@pseudometric_open_subspace_locally_compact R XT hLocal U hOpen.
pose F:=fun i=>@normalised_distribution_scalar_integral R UT Y NY hNY YD edY DNY hYD OY hOY
  DT dvalues (eD (S i)) (rho i) (k i) (hNorm i).
pose H:=@normalised_distribution_scalar_integral R UT Y NY hNY YD edY DNY hYD OY hOY
  DT dvalues (eD T) nu xi hNormT.
have hF i:is_real_integral_functional (rho i)
    (positive_function_lattice (@compactly_supported_continuous_functions R UT)) (F i).
  exact:(@normalised_distribution_scalar_integral_laws R UT Y NY hNY YD edY DNY hYD OY hOY
    DT dvalues (eD (S i)) (rho i) (k i) (hNorm i)).
have hH:is_real_integral_functional nu
    (positive_function_lattice (@compactly_supported_continuous_functions R UT)) H.
  exact:(@normalised_distribution_scalar_integral_laws R UT Y NY hNY YD edY DNY hYD OY hOY
    DT dvalues (eD T) nu xi hNormT).
exact:(@original_gauge_radon_open_lower_limit R UT Y NY DT dvalues
  (fun i=>eD (S i)) (eD T) rho nu F H hULocal
  (fun i=>distribution_representation_measure (normalised_distribution_representation_laws (hNorm i)))
  (fun i=>distribution_representation_radon (normalised_distribution_representation_laws (hNorm i)))
  (distribution_representation_measure (normalised_distribution_representation_laws hNormT))
  (distribution_representation_radon (normalised_distribution_representation_laws hNormT)) hF hH
  (fun i=>@normalised_scalar_integral_original_gauge R UT Y NY hNY YD edY DNY hYD OY hOY
    DT dvalues (eD (S i)) (rho i) (k i) (hNorm i))
  (@normalised_scalar_integral_original_gauge R UT Y NY hNY YD edY DNY hYD OY hOY
    DT dvalues (eD T) nu xi hNormT) hPoint).
Qed.
End DistributionWeakLowerSemicontinuity.
