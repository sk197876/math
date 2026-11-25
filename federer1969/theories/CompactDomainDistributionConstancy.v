(** Federer (1969), 4.1.4, p. 348: the original
    compact-domain reduction, using a proved compact cutoff
    and actual global distribution extension. The conclusion
    concerns every original test on U supported in A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestEvaluation SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP ContinuousTestSmoothingConvergence
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothGlobalTranslationSealed NormDifferentialUP NormOpenDomainLaws
  EuclideanLebesgueDimensions ContinuousDualUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothedKernelDensityFamily
  ContinuousDistributionIntegralAction DistributionIntegralFieldUP
  DistributionDirectionalDerivative NormRegularity ContinuousRealFunctional ContinuousDualSealed SmoothingKernelSealed SmoothingDilationSealed
  ContinuousSmoothSmoothingExistence TestSmoothingFamilyExistence SmoothedDistributionInnerConstancy
  InnerParallelFamilySealed InnerComponentFamilySealed RegularisationConstantRepresentation
  SmoothedKernelIntegralFamily ContinuousDistributionTestLimit PositiveNormLimitUP SummableRealFunctionUP MeasureIntegralUP
  GlobalDistributionConstancy SmoothCompactCutoffSealed SmoothCompactCutoffUP NormRegularityOperations
  CompactSupportFunctionUP CompactTestDistributionExtension CompactTestExtensionLocality TestZeroExtensionSealed
  TestZeroExtensionLaws TestZeroExtensionUP SmoothTestEvaluation LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactDomainDistributionConstancy.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y N hN U DT (smooth_test_value hE)).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).


Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) T.
Variable A:set X.
Hypothesis hOpen:@open (real_norm_metric_space hN) A.
Hypothesis hConnected:@connected (real_norm_metric_space hN) A.
Variable K0:smooth_compact_set hN U.
Hypothesis hAK:A `<=` smooth_compact_carrier K0.
Variable a:X.
Hypothesis ha:A a.
Hypothesis hAnn:forall i:'I_n,forall f:DT,support f `<=` A ->
  T (@distribution_test_directional_derivative R X Y N NY hN hNY U hU E ev hE D hD (@coordinate_basis R n i) f)=0.

(** Source for [compact_domain_distribution_constant]: the
    initial reduction to compact closure in U is valid for
    every connected open A contained in an original compact
    subset of U, Federer 4.1.4, p. 348. The actual cutoff
    extension discharges all premises of the global theorem. *)
Theorem compact_domain_distribution_constant:
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,support f `<=` A ->
      is_measure_integral (@euclidean_lebesgue_measure R n)
        (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (T f)%:E.
Proof.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose B:=@SmoothFunctionSpace.space R X Y N NY hN hNY (fun _=>True) hFull.
pose bv:=@SmoothFunctionSpace.value R X Y N NY hN hNY (fun _=>True) hFull.
pose hB:=@SmoothFunctionSpace.laws R X Y N NY hN hNY (fun _=>True) hFull.
pose DB:=@SmoothFunctionDerivatives.operators R X Y N NY hN hNY (fun _=>True) B bv hB.
pose hDB:=@SmoothFunctionDerivatives.laws R X Y N NY hN hNY (fun _=>True) B bv hB.
pose TB:=smooth_test_space hB.
pose valueB:=smooth_test_value hB.
pose supportB:=@smooth_function_support R X Y N hN (fun _=>True) TB valueB.
pose L:=@TestZeroExtension.operator R X Y N NY hN hNY U (fun _=>True) hFull (fun _ _=>Logic.I) E B ev bv hE hB.
pose hL:=@TestZeroExtension.laws R X Y N NY hN hNY U (fun _=>True) hFull (fun _ _=>Logic.I) E B ev bv hE hB.
pose u:=@SmoothCompactCutoff.value R X N hN n (@coordinate_basis R n) (@coordinate_basisP R n) U K0 hU.
pose hCut:=@SmoothCompactCutoff.laws R X N hN n (@coordinate_basis R n) (@coordinate_basisP R n) U K0 hU.
have hu:norm_class_all_orders hN (@scalar_absolute_value_norm R) U u.
  move=>k.
  exact:(@norm_class_open_restriction R X R^o N (fun t:R^o=>`|t|) hN (@scalar_absolute_value_norm R)
    (fun _=>True) U u k (fun _ _=>Logic.I) hU (smooth_cutoff_class hCut k)).
pose K:=@Build_smooth_compact_set R X N hN U
  (@real_function_support R (real_norm_metric_space hN) u)
  (smooth_cutoff_support_in_domain hCut) (smooth_cutoff_compact hCut).
pose hK:=fun x (hx:@real_function_support R (real_norm_metric_space hN) u x)=>hx.
pose M:=@compact_test_extension_map R X Y N NY hN hNY U hU E B ev bv hE hB u hu K hK.
pose H:=hom_comp M (smooth_test_inclusion hB).
have hOne:forall x,A x ->u x= 1.
  have[W [_ [hKW hOne]]]:=smooth_cutoff_neighbourhood_plateau hCut.
  move=>x hx; exact:(hOne x (hKW x (@hAK x hx))).
have hAU:A `<=` U by move=>x hx; exact:(smooth_compact_in_domain K0 x (@hAK x hx)).
have hMC:=@compact_test_extension_map_continuous R X Y N NY hN hNY U hU E B ev bv hE hB D DB hD hDB u hu K hK.
have hInc:=@smooth_test_inclusion_continuous R X Y N NY hN hNY (fun _=>True) B bv hB DB hDB.
have hHC:=@open_family_continuous_compose TB B DT (smooth_test_opens hB hDB)
  (smooth_function_opens hDB) SO (smooth_test_inclusion hB) M hInc hMC.
pose S:=hom_comp T H.
have hSC:=@open_family_continuous_compose TB DT R^o (smooth_test_opens hB hDB) SO
  (norm_open_family (@scalar_absolute_value_norm R)) H T hHC hT.
have hAnnB:forall i:'I_n,forall g:TB,supportB g `<=` A ->
    S (@distribution_test_directional_derivative R X Y N NY hN hNY (fun _=>True) hFull B bv hB DB hDB
      (@coordinate_basis R n i) g)=0.
  move=>i g hSupp.
  rewrite /S hom_compE.
  rewrite (@compact_test_extension_local_directional R X Y N NY hN hNY U hU E B ev bv hE hB D DB hD hDB
    u hu K hK L hL A hAU hOne (@coordinate_basis R n i) g hSupp).
  apply:(@hAnn i).
  by rewrite (@compact_test_extension_local_support R X Y N NY hN hNY U hU E B ev bv hE hB
    u hu K hK L hL A hAU hOne g hSupp).
have[alpha [hAlpha hRep]]:=@global_distribution_annihilating_derivatives_constant R n Y NY hNY hY
  B bv hB DB hDB S hSC A hOpen hConnected a ha hAnnB.
exists alpha; split=>// f hSupp.
have hExtended:supportB (L f) `<=` A.
  by rewrite /supportB (@test_zero_extension_support R X Y N NY hN hNY U (fun _=>True)
    (fun _ _=>Logic.I) E B ev bv hE hB L hL f).
have hIntegral:=@hRep (L f) hExtended.
have hBack:=@compact_test_extension_local_left_inverse R X Y N NY hN hNY U hU E B ev bv hE hB
  u hu K hK L hL A hAU hOne f hSupp.
have hValues:(fun x=>alpha (valueB (L f) x))=(fun x=>alpha (smooth_test_value hE f x)).
  apply:funext=>x; by rewrite /valueB (@test_zero_extension_value R X Y N NY hN hNY U (fun _=>True)
    E B ev bv hE hB L hL f x).
by rewrite hValues /S hom_compE hBack in hIntegral.
Qed.
End CompactDomainDistributionConstancy.
