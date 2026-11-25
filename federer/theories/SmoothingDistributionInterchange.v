(** Federer (1969), 4.1.2, pp. 347-348:
    the actual smoothed test action is the integral
    against the actual smooth dual-valued kernel density.
    The book's finite Borel partitions approximate both
    sides in the same original compact support step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom ModuleQuotient LinearSubspaceRepresentationUP RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearSealed NormHigherMultiPartialUP PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP MeasureUP MeasureIntegralUP SummableRealFunctionUP
  FiniteCommonRadius HigherDifferentialFinitePartialBound SmoothGlobalTranslationUP
  TranslatedKernelTestUP FiniteKernelPartialQuadrature FiniteKernelTestSumDerivative FiniteKernelTestSumJetApproximation FiniteKernelTestSumSeminormApproximation
  NormOpenTopology OpenFamilyTopologyUP NormOpenDomainLaws
  ContinuousDualUP ContinuousDualNorm NormDualEvaluationBilinear NormClassOneUP
  SmoothFunctionSupport SmoothTestSubspaces SmoothTestEvaluation SmoothTestTopology DistributionSupportedBound
  SmoothedDistributionDensityUP SmoothedDistributionDensityContinuity FiniteTaggedBorelPartitionExistence
  CompactScalarTaggedQuadrature CompactConvolutionSupport CompactKernelTestSumSupport
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothCompactSet SmoothTestSpaces SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothSmoothingPartials
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext TopologicalBorel
  ContinuousFieldLocalIntegrability LocallyIntegrableVectorFieldUP SmoothingConvolutionUP ConvolutionMultiPartialKernel
  FiniteTaggedBorelPartitionUP FiniteTaggedVectorIntegral CompactKernelFieldOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingDistributionInterchange.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable S:lmodType R.
Variable sv:S->X->R^o.
Hypothesis hS:is_smooth_function_space hN hNS (fun _=>True) sv.
Variable DS:forall j,X->Hom S (@ContinuousMultilinear.space R j X R^o N NS hN hNS).
Hypothesis hDS:@is_smooth_function_derivatives R X R^o N NS hN hNS (fun _=>True) S sv DS.
Variable s:S.
Variable psi:X->R.
Hypothesis hPsiValue:forall x,sv s x=psi x.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y N NY hN hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Variable f g:E.
Hypothesis hConv:is_smoothing_convolution hNY psi (ev f) (ev g).
Variable K:smooth_compact_set hN (fun _=>True).
Hypothesis hFOff:forall x,~smooth_compact_carrier K x ->ev f x=0.
Variable b:R.
Hypothesis hMass:mu (smooth_compact_carrier K)=b%:E.
Local Notation ep := (fun j=>@ContinuousMultilinear.evaluation R j X R^o N NS hN hNS).
Local Notation PN := (fun j=>@ContinuousMultilinear.norm R j X R^o N NS hN hNS).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).


Variable L:X->Hom S S.
Hypothesis hL:forall c,is_smooth_global_translation sv c (L c).
Variable B:X->Hom Y (smooth_test_space hE).
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).



Variable T:Hom (smooth_test_space hE) R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD) (norm_open_family hNS) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable xi:X->YD.
Hypothesis hXi:is_smoothed_distribution_density B T ed xi.
Variable C:smooth_compact_set hN (fun _=>True).
Hypothesis hThick:forall x z,smooth_compact_carrier K z ->N (x-z)<=r ->smooth_compact_carrier C x.

(** Source for [smoothing_distribution_integral_interchange]: the
    full original integral/T interchange in Federer 4.1.2,
    pp. 347-348. The finite sums, their
    exact derivatives, common compact support and both
    approximation estimates are proved before this conclusion. *)
Theorem smoothing_distribution_integral_interchange (GTest:smooth_test_space hE):
  smooth_test_inclusion hE GTest=g ->
  is_measure_integral mu
    (real_total_integrand (fun z=>ed (xi z) (ev f z))) (T GTest)%:E.
Proof.
move=>hGTest.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose hDN:=continuous_dual_norm_is_norm hYD.
have hFunction:sv s=psi by apply:funext=>x; exact:hPsiValue.
have hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
  rewrite -hFunction; exact:smooth_function_evaluation_smooth hS s.
have hXiContinuous:=@smoothed_distribution_density_continuous R n Y NY hNY E ev hE D hD
  psi hPsi r hOff B hB T hT YD ed DN hYD xi hXi.
have hFClass0:=smooth_function_evaluation_smooth hE f 0%N.
have hXiClass0:=(@norm_class_zeroP R X YD N DN hN hDN (fun _=>True) xi).2 hXiContinuous.
have hPairClass:=@norm_class_dual_pairing R Y NY hNY YD ed DN hYD X N hN
  (fun _=>True) (ev f) xi 0%N hFClass0 hXiClass0.
pose F z:=ed (xi z) (ev f z).
have hPairOff z:~smooth_compact_carrier K z ->F z=0.
  move=>hz; by rewrite /F (@hFOff z hz) linear0.
have[c [hIntegral hQuadrature]]:=@compact_scalar_tagged_quadrature R n K b hMass F
  (norm_class_continuous hPairClass) hPairOff.
case:(eqVneq (T GTest) c)=>[hEqual|hNe]; first by rewrite hEqual.
exfalso.
pose eta:=`|T GTest-c|.
have hEta:0<eta by rewrite /eta normr_gt0 subr_eq0.
have hBMass:0<=b.
  have h:=measure_nonnegative hm (smooth_compact_carrier K); by rewrite hMass lee_fin in h.
have hBPlus:0<b+1 by lra.
have hGOff:=@compact_convolution_support_bound R X Y N NY hNY mu hm
  (smooth_compact_carrier K) (smooth_compact_carrier C) r psi (ev f) (ev g)
  hOff hThick hFOff hConv.
have hGSupport:@smooth_function_support R X Y N hN (fun _=>True) E ev g `<=` smooth_compact_carrier C.
  exact:(smooth_function_compact_support_iff hE C g).2 hGOff.
have[i [M hLocal]]:=@distribution_supported_local_bound R X Y N NY hN hNY
  (fun _=>True) hFull E ev hE D hD T hT C.
have hM:(0<=(M%:R:R)):=ler0n R M.
have hMPlus:0<(M%:R:R)+1 by lra.
pose qT:=(eta/2)/(M%:R+1).
pose qS:=(eta/2)/(b+1).
have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
have hQT:0<qT by rewrite /qT divr_gt0.
have hQS:0<qS by rewrite /qS divr_gt0.
have[dT [hdT hTestApprox]]:=@finite_kernel_test_sum_seminorm_approximation R n Y NY hNY hY hSep
  S sv hS DS hDS s psi hPsiValue r hOff E ev hE D hD f g hConv K hFOff b hMass
  L hL B hB i C qT hQT.
have[dS [hdS hScalarApprox]]:=hQuadrature qS hQS.
pose mesh:=(Num.min dT dS)/2.
have hMin:0<Num.min dT dS by rewrite lt_min hdT hdS.
have hMesh:0<mesh by rewrite /mesh divr_gt0 // ltr0n.
have hHalfMin:mesh<Num.min dT dS by rewrite /mesh; lra.
have hMinT:Num.min dT dS<=dT by rewrite ge_min lexx.
have hMinS:Num.min dT dS<=dS by rewrite ge_min lexx orbT.
have hMeshT:mesh<dT:=lt_le_trans hHalfMin hMinT.
have hMeshS:mesh<dS:=lt_le_trans hHalfMin hMinS.
have[m [A [tag hPart]]]:=@finite_tagged_compact_borel_partition_exists R n
  (smooth_compact_carrier K) mesh (smooth_compact_is_compact K) hMesh.
pose W:=\sum_i fine (mu (A i))*:B (tag i) (ev f (tag i)).
have hWSupport:=@compact_kernel_test_sum_support R X Y N NY hN hNY E ev hE psi r B
  mu hm K C (ev f) hOff hB hThick (Finite.clone 'I_m _) A tag mesh hPart.
have hSupportError:@smooth_function_support R X Y N hN (fun _=>True) E ev
    (smooth_test_inclusion hE (GTest-W)) `<=` smooth_compact_carrier C.
  change (smooth_fixed_support_subspace hE C (smooth_test_inclusion hE (GTest-W))).
  have hInc:smooth_test_inclusion hE (GTest-W)=g-smooth_test_inclusion hE W.
    have h:=linearB (hom_as_linear (smooth_test_inclusion hE)) GTest W.
    change (smooth_test_inclusion hE (GTest-W)=
      smooth_test_inclusion hE GTest-smooth_test_inclusion hE W) in h.
    by rewrite hGTest in h.
  rewrite hInc.
  exact:(@subspace_sub R E (smooth_fixed_support_subspace hE C) _ _ hGSupport hWSupport).
have hLocalError:=hLocal (GTest-W) hSupportError.
have hIncError:smooth_test_inclusion hE (GTest-W)=g-smooth_test_inclusion hE W.
  have h:=linearB (hom_as_linear (smooth_test_inclusion hE)) GTest W.
  change (smooth_test_inclusion hE (GTest-W)=
    smooth_test_inclusion hE GTest-smooth_test_inclusion hE W) in h.
  by rewrite hGTest in h.
have hEvalError:T (GTest-W)=T GTest-T W.
  exact:(linearB (hom_as_linear T) GTest W).
rewrite hIncError hEvalError in hLocalError.
have hNu:=@hTestApprox (Finite.clone 'I_m _) A tag mesh hPart hMeshT.
have hNuNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hD C i) (g-smooth_test_inclusion hE W).
have hStrict:(M%:R+1)*smooth_function_derivative_seminorm hD C i
    (g-smooth_test_inclusion hE W)<(M%:R+1)*qT.
  by rewrite ltr_pM2l.
have hCancelT:(M%:R+1)*qT=eta/2 by rewrite /qT mulrC divfK // gt_eqF.
rewrite hCancelT in hStrict.
have hTError:`|T GTest-T W|<eta/2.
  apply:le_lt_trans hLocalError _; nra.
have hSum:T W=\sum_i fine (mu (A i))*F (tag i).
  rewrite /W linear_sum; apply:eq_bigr=>j _.
  change (T (fine (mu (A j))*:B (tag j) (ev f (tag j)))=fine (mu (A j))*F (tag j)).
  have hScale:T (fine (mu (A j))*:B (tag j) (ev f (tag j)))=
      fine (mu (A j))*T (B (tag j) (ev f (tag j))).
    exact:(linearZ_LR (hom_as_linear T) _ _).
  by rewrite hScale /F hXi.
have hScalar:=@hScalarApprox (Finite.clone 'I_m _) A tag mesh hPart hMeshS.
have hScalarUpper:qS*b<=qS*(b+1).
  apply:ler_wpM2l; first exact:ltW hQS.
  by lra.
have hCancelS:qS*(b+1)=eta/2 by rewrite /qS divfK // gt_eqF.
rewrite hCancelS in hScalarUpper.
have hSError:`|c-T W|<=eta/2.
  rewrite hSum; exact:le_trans hScalar hScalarUpper.
have hDecomposition:T GTest-c=(T GTest-T W)+(T W-c) by rewrite addrA subrK.
have hTriangle:`|T GTest-c|<=`|T GTest-T W|+`|c-T W|.
  have h:=ler_normD (T GTest-T W) (T W-c).
  by rewrite -hDecomposition (real_seminorm_subtract hNS.1 (T W) c) in h.
have hLess:`|T GTest-c|<eta by nra.
by move:hLess; rewrite /eta ltxx.
Qed.
End SmoothingDistributionInterchange.
