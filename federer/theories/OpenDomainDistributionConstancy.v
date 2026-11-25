(** Federer (1969), 4.1.4, pp. 348–349: the complete
    open-domain localization and connected patching argument.
    It uses the original compact cutoff reduction, proved
    compact exhaustions and actual test-integral comparisons. *)
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
  TestZeroExtensionLaws TestZeroExtensionUP SmoothTestEvaluation LinearBasis
  CompactDomainDistributionConstancy DomainConstantFunctionalUniqueness SmoothCompactExhaustionSealed
  CompactExhaustionConnectedNeighbourhood NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenDomainDistributionConstancy.
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

Hypothesis hAU:A `<=` U.
Variable a:X.
Hypothesis ha:A a.
Hypothesis hAnn:forall i:'I_n,forall f:DT,support f `<=` A ->
  T (@distribution_test_directional_derivative R X Y N NY hN hNY U hU E ev hE D hD (@coordinate_basis R n i) f)=0.

(** Source for [open_domain_distribution_annihilating_derivatives_constant]:
    the original arbitrary-open-domain constancy assertion
    of Federer 4.1.4, pp. 348–349. Relatively compact connected
    subdomains supply the local functionals; their actual
    unit tests and connected overlap give one functional for
    every original test supported in A. *)
Theorem open_domain_distribution_annihilating_derivatives_constant:
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,support f `<=` A ->
      is_measure_integral (@euclidean_lebesgue_measure R n)
        (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (T f)%:E.
Proof.
pose NT:=real_norm_metric_space hN.
have hAInterior:forall x,A x ->norm_domain_interior N A x.
  move=>x hx.
  have hNbhs:nbhs (x:NT) A by move:hOpen; rewrite openE; exact.
  exact:(@norm_domain_interior_neighbourhood R X N hN A x).2 hNbhs.
pose K:=@SmoothCompactExhaustion.value R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) A hAInterior.
pose hK:=@SmoothCompactExhaustion.laws R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) A hAInterior.
have hLocal:forall C:smooth_compact_set hN A,exists W:set X,exists alpha:Hom Y R^o,
    @open NT W /\ W a /\ (W `<=` A) /\ (smooth_compact_carrier C `<=` W) /\
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,support f `<=` W ->
      is_measure_integral (@euclidean_lebesgue_measure R n)
        (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (T f)%:E.
  move=>C.
  have[W [hWOpen [hWConnected [hWa [hCW [hClosureCompact hClosureA]]]]]]:=
    @compact_exhaustion_connected_neighbourhood R X N hN A hConnected K hK a ha C.
  have hWA:W `<=` A.
    move=>x hx; exact:(hClosureA x (@subset_closure NT W x hx)).
  have hClosureU:@closure NT W `<=` U.
    move=>x hx; exact:(@hAU x (hClosureA x hx)).
  pose K0:=@Build_smooth_compact_set R X N hN U (@closure NT W) hClosureU hClosureCompact.
  have hWK:W `<=` smooth_compact_carrier K0.
    exact:(@subset_closure NT W).
  have hAnnW:forall i:'I_n,forall f:DT,support f `<=` W ->
      T (@distribution_test_directional_derivative R X Y N NY hN hNY U hU E ev hE D hD (@coordinate_basis R n i) f)=0.
    move=>i f hSupp; apply:(@hAnn i f)=>x hx.
    exact:(hWA x (hSupp x hx)).
  have[alpha [hAlpha hRep]]:=@compact_domain_distribution_constant R n Y NY hNY hY E ev U hU hE D hD
    T hT W hWOpen hWConnected K0 hWK a hWa hAnnW.
  exists W,alpha; split; first exact hWOpen.
  split; first exact hWa.
  split; first exact hWA.
  split; first exact hCW.
  by split.
pose C0:=@smooth_compact_singleton R X N hN A a ha.
have[W0 [alpha0 [hW0Open [hW0a [hW0A [hC0W0 [hAlpha0 hRep0]]]]]]]:=@hLocal C0.
exists alpha0; split=>// f hSupp.
pose C:=@Build_smooth_compact_set R X N hN A (support f) hSupp (smooth_test_support_compact hE f).
have[W [alpha [hWOpen [hWa [hWA [hCW [hAlpha hRep]]]]]]]:=@hLocal C.
have hMeetU:(W `&` W0) `<=` U.
  move=>x [hx _]; exact:(@hAU x (hWA x hx)).
have hRepMeet:forall g:DT,support g `<=` (W `&` W0) ->
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (fun x=>alpha (smooth_test_value hE g x))) (T g)%:E.
  move=>g hg; apply:hRep=>x hx; exact:(hg x hx).1.
have hRepMeet0:forall g:DT,support g `<=` (W `&` W0) ->
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (fun x=>alpha0 (smooth_test_value hE g x))) (T g)%:E.
  move=>g hg; apply:hRep0=>x hx; exact:(hg x hx).2.
have hSame:alpha=alpha0:=@domain_constant_functional_unique R n Y NY hNY hY U hU E ev hE
  (W `&` W0) (openI hWOpen hW0Open) hMeetU a (conj hWa hW0a) T alpha alpha0
  hAlpha hAlpha0 hRepMeet hRepMeet0.
rewrite -hSame; apply:hRep; exact hCW.
Qed.
End OpenDomainDistributionConstancy.
