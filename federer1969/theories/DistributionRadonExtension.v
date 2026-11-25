(** Federer (1969), 4.1.5, p. 350: the
    original compact continuous extension has a Radon
    variation measure and a normalized weakly measurable
    dual density. The earlier 2.5.14 representation
    theorem supplies both after all its hypotheses
    have been proved for the actual fields on U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology CompleteMetricUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses VectorDaniellNormalisationUP
  MeasureUP RadonMeasureUP RealIntegralFunctionalUP SubtypeCompactHausdorff OpenSubspaceMeasure
  CompactContinuousVectorFields CompactContinuousVectorSpace CompactContinuousVectorModule
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionFiniteVariationUP
  DistributionContinuousExtensionUP DistributionSubspaceExtension RadonVectorRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionRadonExtension.
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
Local Notation Q := (@compact_continuous_vector_fields R UT Y NY hNY).
Variable S:Hom DT R^o.
Hypothesis hFinite:@is_finite_distribution_variation R XT U Y NY DT values S.
Variable T:(X->Y)->R.
Hypothesis hT:@is_distribution_continuous_extension R XT U Y NY hNY DT values S T.
Local Notation TU := (@distribution_subspace_extension R XT U Y T).

(** Source for [distribution_radon_extension_representation]:
    the actual Radon measure and normalized weak dual
    density for the original T of Federer 4.1.5,
    p. 350. No unit series, global dual separability
    or additional order-bound hypothesis is imposed. *)
Theorem distribution_radon_extension_representation:
  exists rho:set UT->\bar R,exists k:UT->weak_dual_space hNY,
    is_measure rho /\ is_radon_measure rho /\
    is_real_integral_functional rho
      (positive_function_lattice (@compactly_supported_continuous_functions R UT))
      (variation_integral NY Q TU) /\
    is_normalised_vector_daniell_density rho Q TU k.
Proof.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hLocal:=@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN.
have hHausdorff:=@set_type_hausdorff XT U (@metric_hausdorff R XT).
have hULocal:=@pseudometric_open_subspace_locally_compact R XT hLocal U hOpen.
have hQ:=@compact_continuous_vector_space R UT Y NY hNY.
have hM:=@compact_continuous_vector_lattice_module R UT Y NY hNY.
have hBounded:=@distribution_subspace_extension_order_bounded R n Y NY hNY hY U hU E ev hE S hFinite T hT.
exact:(@radon_vector_variation_representation R UT Y NY hNY hSeparable Q TU
  hHausdorff hULocal hQ hM hBounded).
Qed.
End DistributionRadonExtension.
