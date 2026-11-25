(** Federer (1969), 4.1.5, p. 350:
    if mu is a scalar Daniell integral
    on K(U), its restriction to the
    original D(U,R) is an actual distribution.
    The original finite gauge proves continuity
    for the literal final test topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  FunctionLatticeUP CompactSupportFunctionUP DaniellIntegralUP DistributionVariationDomain
  DistributionFiniteVariationUP ScalarDaniellRestrictionUP DaniellLinearTestRestriction
  SmoothScalarTestCompactFunction FiniteGaugeDistributionContinuity ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarDaniellDistribution.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation XT := (real_norm_metric_space hN).
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->R^o.
Hypothesis hE:is_smooth_function_space hN hNS U ev.
Variable D:forall k,X->Hom E (@ContinuousMultilinear.space R k X R^o N (fun t:R^o=>`|t|) hN hNS).
Hypothesis hD:@is_smooth_function_derivatives R X R^o N (fun t:R^o=>`|t|) hN hNS U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U R^o DT values).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Variable A:(UT->R)->R.
Hypothesis hA:is_daniell_integral (@compactly_supported_continuous_functions R UT) A.

(** Source for [scalar_daniell_restriction_finite_gauge]: the
    original scalar restriction has finite
    scalar-test gauge, Federer 4.1.5, p. 350. *)
Theorem scalar_daniell_restriction_finite_gauge (S:Hom DT R^o):
  @is_scalar_daniell_test_restriction R UT DT dvalues A S ->
  @is_finite_distribution_variation R XT U R^o (fun t:R^o=>`|t|) DT values S.
Proof.
exact:(@daniell_linear_test_restriction_finite R UT DT dvalues
  (fun phi=>@smooth_scalar_test_original_compact_function R X N hN U E ev hE phi) A hA S).
Qed.

(** Source for [scalar_daniell_restriction_continuous]: the
    original scalar restriction is continuous
    for Federer's literal final test topology,
    Federer 4.1.5, p. 350. *)
Theorem scalar_daniell_restriction_continuous (S:Hom DT R^o):
  @is_scalar_daniell_test_restriction R UT DT dvalues A S ->
  open_family_continuous SO (norm_open_family hNS) S.
Proof.
move=>hRestriction.
exact:(@finite_gauge_distribution_continuous R n R^o (fun t:R^o=>`|t|) hNS U hU E ev hE D hD S
  (scalar_daniell_restriction_finite_gauge hRestriction)).
Qed.

(** Source for [scalar_daniell_distribution_exists]: an actual
    member of D'(U,R) has precisely the
    original scalar Daniell values on every
    test, Federer 4.1.5, p. 350. *)
Theorem scalar_daniell_distribution_exists:
  exists T:DD,@is_scalar_daniell_test_restriction R UT DT dvalues A (eD T).
Proof.
have[S hRestriction]:=@daniell_linear_test_restriction_exists R UT DT dvalues
  (fun phi=>@smooth_scalar_test_original_compact_function R X N hN U E ev hE phi) A hA.
have hContinuous:=scalar_daniell_restriction_continuous hRestriction.
have[T hEvaluation]:=@continuous_real_dual_represents R DT SO hSO S hContinuous.
exists T; by rewrite hEvaluation.
Qed.
End ScalarDaniellDistribution.
