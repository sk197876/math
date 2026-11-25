(** Federer (1969), 4.1.5, p. 350:
    the original gauge of a scalar Daniell
    restriction is mu+ + mu-. The compact
    extension agrees with the original functional,
    and the proved 2.5.6 symmetric-interval
    supremum gives both exact inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  GrassmannAbbreviations FiniteCoordinates LinearBasis EuclideanInnerProduct InnerNorm HilbertFormCompactness
  IsotropyGroupTopology FiniteNormEquivalence ScalarNormMetricCompleteness SubtypeCompactHausdorff OpenSubspaceMeasure
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation FunctionLatticeUP CompactSupportFunctionUP
  DaniellIntegralUP ScalarDaniellRestrictionUP SmoothScalarTestCompactFunction
  CompactScalarVectorIdentification CompactContinuousVectorFields CompactContinuousDomainFields
  CompactContinuousVectorZeroExtension CompactContinuousOpenExtensionLinear CompactContinuousSubspaceSupport CompactContinuousTestApproximation
  CompactUniformApproximationUP CompactUniformDaniellLimit PositiveNormLimitUP
  DistributionVariationDomain DistributionSubspaceExtension DistributionContinuousExtensionUP
  DaniellLinearTestRestriction DistributionFiniteVariationUP DistributionVariationUP DistributionVariationBasic
  DistributionContinuousExtensionSealed ScalarDaniellCompactExtension CompactUniformNorm VectorFunctionLattice
  VectorVariationFiniteBounds DaniellVariationUP DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarDaniellDistributionVariation.
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
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U R^o DT values).
Variable A:(UT->R)->R.
Hypothesis hA:is_daniell_integral (@compactly_supported_continuous_functions R UT) A.
Variable S:Hom DT R^o.
Hypothesis hRestriction:@is_scalar_daniell_test_restriction R UT DT dvalues A S.
Variable P Q:(UT->R)->R.
Hypothesis hP:is_daniell_positive_variation (@compactly_supported_continuous_functions R UT) A P.
Hypothesis hQ:is_daniell_negative_variation (@compactly_supported_continuous_functions R UT) A Q.

(** Source for [scalar_daniell_distribution_variation]: the exact
    ||S||=mu+ + mu- assertion in Federer
    4.1.5, p. 350, on the original
    K(U)+ domain, by 2.5.6, p. 98.
    Every original scalar test is retained. *)
Theorem scalar_daniell_distribution_variation (f:UT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R UT) f ->
  is_distribution_variation_value (fun t:R^o=>`|t|) dvalues S f ((P f+Q f)%:E).
Proof.
move=>hf.
have hTest phi:=@smooth_scalar_test_original_compact_function R X N hN U E ev hE phi.
have hFinite:@is_finite_distribution_variation R XT U R^o (fun t:R^o=>`|t|) DT values S.
  exact:(@daniell_linear_test_restriction_finite R UT DT dvalues hTest A hA S hRestriction).
pose T:=@DistributionContinuousExtension.value R n R^o (fun t:R^o=>`|t|) hNS
  (@scalar_norm_metric_complete R) U hU E ev hE S hFinite.
have hT:=@DistributionContinuousExtension.laws R n R^o (fun t:R^o=>`|t|) hNS
  (@scalar_norm_metric_complete R) U hU E ev hE S hFinite.
have hComparison:=@scalar_daniell_compact_extension_agrees R n U hU E ev hE A hA S hRestriction T hT.
have hK:=@compact_support_vector_lattice R UT.
have[b hGauge]:=@hFinite f hf.
have hUpper:(b%:E<=(P f+Q f)%:E)%E.
  apply:(@distribution_variation_least_finite_bound R UT R^o (fun t:R^o=>`|t|)
    DT dvalues S f b%:E (P f+Q f) hGauge)=>phi hNorm.
  have hBound:=@finite_variation_sum_upper R UT _ A hK (daniell_integral_add hA)
    f (P f) (Q f) hf (@hP f hf) (@hQ f hf) (dvalues phi) (conj (hTest phi) hNorm).
  rewrite (@hRestriction phi); exact:le_trans (ler_norm _) hBound.
rewrite lee_fin in hUpper.
have hLower:P f+Q f<=b.
  apply:(@finite_variation_sum_least R UT _ A hK (daniell_integral_add hA)
    f (P f) (Q f) b (@hP f hf) (@hQ f hf))=>w [hw hNorm].
  have hField:=@compact_function_to_scalar_field R UT w hw.
  have hPlus:=@distribution_subspace_extension_original_bound R n R^o (fun t:R^o=>`|t|)
    hNS (@scalar_norm_metric_complete R) U hU E ev hE S hFinite T hT f b hf hGauge w hField hNorm.
  rewrite (hComparison w hw) in hPlus.
  have hNegative:=@compactly_supported_opp R UT w hw.
  have hNegativeField:=@compact_function_to_scalar_field R UT (fun x=>-w x) hNegative.
  have hNegativeNorm:forall x:UT,`|-w x|<=f x by move=>x; rewrite normrN; exact:hNorm.
  have hMinus:=@distribution_subspace_extension_original_bound R n R^o (fun t:R^o=>`|t|)
    hNS (@scalar_norm_metric_complete R) U hU E ev hE S hFinite T hT f b hf hGauge
    (fun x=>-w x) hNegativeField hNegativeNorm.
  rewrite (hComparison _ hNegative) (@daniell_compact_support_opp R UT A w hA hw) in hMinus.
  rewrite ler_norml; apply/andP; split=>//; by rewrite lerNl.
have hEquality:b = P f+Q f by apply/eqP; rewrite eq_le hUpper hLower.
by rewrite -hEquality.
Qed.
End ScalarDaniellDistributionVariation.
