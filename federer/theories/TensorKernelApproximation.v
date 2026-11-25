(** Federer (1969), 4.1.3, p. 348: tensor image density
    follows from the actual finite Borel sums and their compact
    support and derivative estimates in 4.1.2. The neighbourhood
    conclusion uses the literal final test topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearSealed NormHigherMultiPartialUP PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP MeasureUP
  FiniteCommonRadius HigherDifferentialFinitePartialBound SmoothGlobalTranslationUP
  TranslatedKernelTestUP FiniteKernelPartialQuadrature FiniteKernelTestSumDerivative FiniteKernelTestSumJetApproximation
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothCompactSet SmoothTestSpaces SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothSmoothingPartials
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext TopologicalBorel
  ContinuousFieldLocalIntegrability LocallyIntegrableVectorFieldUP SmoothingConvolutionUP ConvolutionMultiPartialKernel
  FiniteTaggedBorelPartitionUP FiniteTaggedVectorIntegral CompactKernelFieldOscillation SmoothDerivativeSeminormLaws SmoothTestTopology SmoothFunctionSupport
  SmoothTestEvaluation CompactConvolutionSupport CompactKernelTestSumSupport FiniteTaggedBorelPartitionExistence
  TestCommonSupportApproximation FiniteTensorImageSums ContinuousFiniteKernelSeminormApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TensorKernelApproximation.
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


Variable C:smooth_compact_set hN (fun _=>True).
Hypothesis hThick:forall x z,smooth_compact_carrier K z ->
  N (x-z)<=r ->smooth_compact_carrier C x.
Variable W:lmodType R.
Variable F:Hom W (smooth_test_space hE).
Hypothesis hImage:forall z y,exists w:W,F w=B z y.

(** Source for [tensor_kernel_approximation_neighbourhood]:
    the actual finite Borel sums belonging to the canonical
    tensor image meet every neighbourhood of the smoothing,
    Federer 4.1.3, p. 348, using the same-compact estimates
    proved on the preceding page in 4.1.2. *)
Theorem tensor_kernel_approximation_neighbourhood
    (GTest:smooth_test_space hE):
  smooth_test_inclusion hE GTest=g ->
  forall V,smooth_test_opens hE hD V ->V GTest ->
    exists w:W,V (F w).
Proof.
move=>hGTest.
have hGOff:=@compact_convolution_support_bound R X Y N NY hNY mu hm
  (smooth_compact_carrier K) (smooth_compact_carrier C) r psi (ev f) (ev g)
  hOff hThick hFOff hConv.
have hGSupport:@smooth_function_support R X Y N hN (fun _=>True) E ev
    (smooth_test_inclusion hE GTest) `<=` smooth_compact_carrier C.
  rewrite hGTest; exact:(smooth_function_compact_support_iff hE C g).2 hGOff.
have hApprox (L0:smooth_compact_set hN (fun _=>True)) i eta:
    0<eta ->exists h:smooth_test_space hE,
      (exists w:W,F w=h) /\
      @smooth_function_support R X Y N hN (fun _=>True) E ev
        (smooth_test_inclusion hE h) `<=` smooth_compact_carrier C /\
      smooth_function_derivative_seminorm hD L0 i
        (smooth_test_inclusion hE h-smooth_test_inclusion hE GTest)<eta.
  move=>hEta.
  have[d [hd hApprox]]:=@continuous_finite_kernel_seminorm_approximation R n Y NY hNY hY
    S sv hS DS hDS s psi hPsiValue r hOff E ev hE D hD f g hConv K hFOff b hMass L hL B hB
    i L0 eta hEta.
  have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
  have hSmall:d/2<d by rewrite ltr_pdivrMr ?ltr0n //; lra.
  have[m [A [tag hPart]]]:=@finite_tagged_compact_borel_partition_exists R n
    (smooth_compact_carrier K) (d/2) (smooth_compact_is_compact K) hHalf.
  pose I:=Finite.clone 'I_m _.
  pose H:=\sum_(j:I) fine (mu (A j))*:B (tag j) (ev f (tag j)).
  have hHSupport:=@compact_kernel_test_sum_support R X Y N NY hN hNY E ev hE psi r B mu hm
    K C (ev f) hOff hB hThick I A tag (d/2) hPart.
  have hSem:=@hApprox I A tag (d/2) hPart hSmall.
  exists H; split.
  - exact:(@finite_tensor_image_sum R W (smooth_test_space hE) F I
      (fun j=>fine (mu (A j))) (fun j=>B (tag j) (ev f (tag j)))
      (fun j=>hImage (tag j) (ev f (tag j)))).
  split; first exact hHSupport.
  have hNu:=@smooth_derivative_seminorm_is_seminorm R X Y N NY hN hNY (fun _=>True)
    E D L0 i (smooth_function_derivative_seminorm hD L0 i)
    (smooth_function_derivative_seminorm_laws hD L0 i).
  by rewrite (real_seminorm_subtract hNu) hGTest.
move=>V hV hVG.
have[h [[w hw] hVH]]:=@test_common_support_approximation_neighbourhood R X Y N NY hN hNY
  (fun _=>True) E ev hE D hD [set h|exists w:W,F w=h] GTest C hGSupport hApprox V hV hVG.
exists w; by rewrite hw.
Qed.
End TensorKernelApproximation.
