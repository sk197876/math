(** Federer (1969), 4.1.4, pp. 348–349, using 4.1.2, pp. 347-348:
    the actual test smoothing functional has its original
    integral action against the smooth dual-valued density.
    The compact bound is proved for each original test. *)
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
  ContinuousDistributionInterchange SmoothCompactThickening FiniteCoordinates SmoothSmoothingFamilyUP DistributionIntegralFieldUP
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
Section ContinuousDistributionIntegralAction.
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


Hypothesis hRadius:0<=r.
Variable P:Hom E E.
Hypothesis hP:is_smooth_smoothing_operator hNY ev psi P.
Variable Q:Hom (smooth_test_space hE) (smooth_test_space hE).
Hypothesis hQ:forall f,smooth_test_inclusion hE (Q f) = P (smooth_test_inclusion hE f).

(** Source for [continuous_distribution_integral_action]: the original
    equality T(Phi*f)=integral <f,g> for every
    actual test, Federer 4.1.2, pp. 347-348.
    Its common compact support and finite cell masses
    are discharged from the test's actual compact support. *)
Theorem continuous_distribution_integral_action:
  is_distribution_integral_action mu ed xi (smooth_test_value hE) (hom_comp T Q).
Proof.
move=>f.
have[K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
have hFOff x:~smooth_compact_carrier K x ->ev (smooth_test_inclusion hE f) x=0.
  exact:(smooth_function_compact_support_iff hE K _).1 hK x.
have hFinite:=@euclidean_distribution_measure_compact_finite R n
  (smooth_compact_carrier K) (smooth_compact_is_compact K).
have hNonnegative:=measure_nonnegative hm (smooth_compact_carrier K).
have hFin:mu (smooth_compact_carrier K) \is a fin_num by rewrite ge0_fin_numE.
pose b:=fine (mu (smooth_compact_carrier K)).
have hMass:mu (smooth_compact_carrier K)=b%:E by rewrite /b fineK.
have[C [_ hThick]]:=@smooth_compact_thickening R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) K r hRadius.
change (is_measure_integral mu
  (real_total_integrand (fun z=>ed (xi z) (ev (smooth_test_inclusion hE f) z))) (T (Q f))%:E).
exact:(@continuous_distribution_integral_interchange R n Y NY hNY hY
  S sv hS DS hDS s psi hPsiValue r hOff E ev hE D hD
  (smooth_test_inclusion hE f) (P (smooth_test_inclusion hE f)) (@hP (smooth_test_inclusion hE f))
  K hFOff b hMass L hL B hB T hT YD ed DN hYD xi hXi C hThick (Q f) (@hQ f)).
Qed.
End ContinuousDistributionIntegralAction.
