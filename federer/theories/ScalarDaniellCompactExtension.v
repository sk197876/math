(** Federer (1969), 4.1.5, p. 350:
    the compact continuous extension of the
    scalar Daniell restriction is the original
    Daniell functional. Both values are limits
    of the same actual test approximants;
    the fixed-support bound proves the latter limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  GrassmannAbbreviations FiniteCoordinates LinearBasis EuclideanInnerProduct InnerNorm HilbertFormCompactness
  IsotropyGroupTopology FiniteNormEquivalence ScalarNormMetricCompleteness SubtypeCompactHausdorff OpenSubspaceMeasure
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation FunctionLatticeUP CompactSupportFunctionUP
  DaniellIntegralUP ScalarDaniellRestrictionUP SmoothScalarTestCompactFunction
  CompactScalarVectorIdentification CompactContinuousVectorFields CompactContinuousDomainFields
  CompactContinuousVectorZeroExtension CompactContinuousOpenExtensionLinear CompactContinuousSubspaceSupport CompactContinuousTestApproximation
  CompactUniformApproximationUP CompactUniformDaniellLimit PositiveNormLimitUP
  DistributionVariationDomain DistributionSubspaceExtension DistributionContinuousExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarDaniellCompactExtension.
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
Variable T:(X->R^o)->R.
Hypothesis hT:@is_distribution_continuous_extension R XT U R^o (fun t:R^o=>`|t|) hNS DT values S T.

(** Source for [scalar_daniell_compact_extension_agrees]: the
    original Daniell integral is the compact
    continuous extension of its scalar test
    restriction, Federer 4.1.5, p. 350. *)
Theorem scalar_daniell_compact_extension_agrees (w:UT->R):
  compactly_supported_continuous_functions w ->
  @distribution_subspace_extension R XT U R^o T w=A w.
Proof.
move=>hW.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hLocal:=@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN.
have hHausdorff:=@set_type_hausdorff XT U (@metric_hausdorff R XT).
have hULocal:=@pseudometric_open_subspace_locally_compact R XT hLocal U hOpen.
have hWField:=@compact_function_to_scalar_field R UT w hW.
pose W:=@compact_vector_open_extension R XT U R^o w.
have hWGlobal:=@compact_vector_open_extension_domain R XT U R^o (fun t:R^o=>`|t|)
  hNS (@metric_hausdorff R XT) hOpen w hWField.
have[P hApprox]:=@compact_continuous_field_test_approximation R n R^o (fun t:R^o=>`|t|)
  hNS (@scalar_norm_metric_complete R) U hU E ev hE W hWGlobal.1 hWGlobal.2.
have hOriginal:=@distribution_extension_limit R XT U R^o (fun t:R^o=>`|t|) hNS DT values S T hT W hWGlobal P hApprox.
move:hApprox=>[C [hC [hCU [r [hR [hZero hUniform]]]]]].
pose C0:set UT:=(fun x:UT=>set_val x) @^-1` C.
have hC0:compact C0:=@set_type_compact_preimage XT U C hC hCU.
have hTests e:0<e ->compactly_supported_continuous_functions (dvalues (P e)).
  move=>_; exact:(@smooth_scalar_test_original_compact_function R X N hN U E ev hE (P e)).
have hZeroRestricted e:0<e ->e<r ->forall x:UT,~C0 x ->dvalues (P e) x=0.
  move=>hEPositive hSmall x hOutside.
  exact:hZero e hEPositive hSmall (set_val x) hOutside.
have hUniformRestricted eta:0<eta ->exists d:R,0<d /\forall e:R,0<e ->e<d ->forall x:UT,
    `|dvalues (P e) x-w x|<eta.
  move=>hEta; have[d [hD hClose]]:=hUniform eta hEta.
  exists d; split=>// e hEPositive hSmall x.
  have hValue:W (set_val x)=w x:=@compact_vector_open_extension_value R XT U R^o w x.
  have h:=hClose e hEPositive hSmall (set_val x).
  change (is_true (`|dvalues (P e) x-W (set_val x)|<eta)) in h.
  by rewrite hValue in h.
have hDaniell:=@compact_uniform_daniell_positive_limit R UT A w (fun e=>dvalues (P e)) C0 r
  hHausdorff hULocal hA hW hC0 hR hTests hZeroRestricted hUniformRestricted.
have hEquality:(fun e=>S (P e))=(fun e=>A (dvalues (P e))).
  apply:funext=>e; exact:(@hRestriction (P e)).
rewrite hEquality in hOriginal.
exact:(@positive_norm_limit_unique R R^o (fun t:R^o=>`|t|) hNS
  (fun e=>A (dvalues (P e))) (T W) (A w) hOriginal hDaniell).
Qed.
End ScalarDaniellCompactExtension.
