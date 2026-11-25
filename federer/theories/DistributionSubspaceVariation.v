(** Federer (1969), 4.1.5, p. 350: the
    original gauge equals the variation integral of
    the compact continuous extension. The compactness
    argument of 2.5.14 supplies sequential continuity;
    the proved sharp bound supplies the reverse
    inequality between the two original suprema. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology CompleteMetricUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses VectorDaniellVariationIntegral
  SubtypeCompactHausdorff OpenSubspaceMeasure CompactSupportVectorContinuity
  CompactContinuousVectorFields CompactContinuousVectorSpace CompactContinuousVectorModule
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationUP DistributionVariationBasic
  DistributionVariationDomain DistributionFiniteVariationUP DistributionContinuousExtensionUP
  DistributionSubspaceExtension DistributionSubspaceTestValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionSubspaceVariation.
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
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation L := (@compactly_supported_continuous_functions R UT).
Local Notation Q := (@compact_continuous_vector_fields R UT Y NY hNY).
Variable S:Hom DT R^o.
Hypothesis hFinite:@is_finite_distribution_variation R XT U Y NY DT values S.
Variable T:(X->Y)->R.
Hypothesis hT:@is_distribution_continuous_extension R XT U Y NY hNY DT values S T.
Local Notation TU := (@distribution_subspace_extension R XT U Y T).

(** Source for [distribution_subspace_variation_functional]:
    the second clause of 2.5.12(5) follows from its
    first clause by the compact-support argument of
    2.5.14, as stated in Federer 4.1.5, p. 350. *)
Theorem distribution_subspace_variation_functional:
  is_vector_variation_functional NY L Q TU.
Proof.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hLocal:=@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN.
have hHausdorff:=@set_type_hausdorff XT U (@metric_hausdorff R XT).
have hULocal:=@pseudometric_open_subspace_locally_compact R XT hLocal U hOpen.
exact:(@compact_support_vector_variation_functional R UT Y NY hNY Q TU hHausdorff hULocal
  (@compact_continuous_vector_space R UT Y NY hNY)
  (@compact_continuous_vector_lattice_module R UT Y NY hNY)
  (@distribution_subspace_extension_order_bounded R n Y NY hNY hY U hU E ev hE S hFinite T hT)).
Qed.

(** Source for [distribution_original_gauge_variation_value]:
    ||S|| equals the original Daniell variation integral
    of T, Federer 4.1.5, p. 350. This is the
    literal K(U)+ gauge and is proved before any
    notation identifies it with its representing measure. *)
Theorem distribution_original_gauge_variation_value f:
  positive_function_lattice L f ->
  is_distribution_variation_value NY dvalues S f (variation_integral NY Q TU f)%:E.
Proof.
move=>hf.
have[b hGauge]:=@hFinite f hf.
have hQ:=@compact_continuous_vector_space R UT Y NY hNY.
have hV:=distribution_subspace_variation_functional.
have hUpper:variation_integral NY Q TU f<=b.
  apply:(@variation_integral_least R UT Y NY hNY L Q TU hQ f b hf)=>w hw hBound.
  exact:(@distribution_subspace_extension_original_bound R n Y NY hNY hY U hU E ev hE S hFinite T hT
    f b hf hGauge w hw hBound).
have hLower:(b%:E<=(variation_integral NY Q TU f)%:E)%E.
  apply:(@distribution_variation_least_finite_bound R UT Y NY DT dvalues S f b%:E
    (variation_integral NY Q TU f) hGauge)=>phi hBound.
  have hMember:=@smooth_test_original_continuous_field R X Y N NY hN hNY U E ev hE phi.
  have h:=@variation_integral_upper R UT Y NY hNY L Q TU hQ hV f (dvalues phi) hf hMember hBound.
  by rewrite (@distribution_subspace_test_value R X Y N NY hN hNY U E ev hE S T hT phi) in h.
rewrite lee_fin in hLower.
have hEq:variation_integral NY Q TU f=b by apply/eqP; rewrite eq_le hUpper hLower.
by rewrite hEq.
Qed.
End DistributionSubspaceVariation.
