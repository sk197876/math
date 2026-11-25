(** Federer (1969), 4.1.2, p. 348: the
    actual tagged finite test sum approaches the convolution
    uniformly in every full derivative on compact sets.
    The original finite-coordinate reconstruction assembles
    the already proved exact partial integral estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearSealed NormHigherMultiPartialUP PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP MeasureUP
  FiniteCommonRadius HigherDifferentialFinitePartialBound SmoothGlobalTranslationUP
  TranslatedKernelTestUP FiniteKernelPartialQuadrature FiniteKernelTestSumDerivative
  SmoothCompactSet SmoothTestSpaces SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothSmoothingPartials
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext TopologicalBorel
  ContinuousFieldLocalIntegrability LocallyIntegrableVectorFieldUP SmoothingConvolutionUP ConvolutionMultiPartialKernel
  FiniteTaggedBorelPartitionUP FiniteTaggedVectorIntegral CompactKernelFieldOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteKernelTestSumJetApproximation.
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

(** Source for [finite_kernel_test_sum_jet_approximation]: uniform
    approximation of each full original derivative by
    the finite Borel sums in Federer 4.1.2,
    p. 348. Zero compact mass and zero
    dimension are retained. *)
Theorem finite_kernel_test_sum_jet_approximation k
    (C:smooth_compact_set hN (fun _=>True)) (eta:R):
  0<eta ->exists d:R,0<d /\ forall (I:finType) (A:I->set X) (tag:I->X) (mesh:R),
    @is_finite_tagged_borel_partition R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag ->mesh<d ->
    forall x,smooth_compact_carrier C x ->
      @ZN k (@D k x (g-smooth_test_inclusion hE
        (\sum_i fine (mu (A i))*:B (tag i) (ev f (tag i)))))<=eta.
Proof.
move=>hEta.
have[M [hM hReconstruction]]:=@norm_higher_differential_finite_partial_bound R n Y NY hNY Z ez ZN hZ k.
have hBMass:0<=b.
  have h:=measure_nonnegative hm (smooth_compact_carrier K).
  by rewrite hMass lee_fin in h.
have hBPositive:0<b+1 by lra.
have hDen:0<M*(b+1) by rewrite mulr_gt0.
pose qEta:=eta/(M*(b+1)).
have hQEta:0<qEta by rewrite /qEta divr_gt0.
pose P (alpha:symmetric_indices n k) (mesh:R):Prop:=
  forall (I:finType) (A:I->set X) (tag:I->X),
    @is_finite_tagged_borel_partition R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag ->
    forall x,smooth_compact_carrier C x ->
      NY (@ez k (norm_multi_partial_arguments R alpha) (@D k x g)-
        \sum_i fine (mu (A i))*:
          ((@ep k (norm_multi_partial_arguments R alpha) (@DS k (x-tag i) s))*:ev f (tag i)))<=qEta*b.
have hEach alpha:exists d:R,0<d /\ forall mesh:R,mesh<d ->P alpha mesh.
  have[d [hd hBound]]:=@finite_kernel_partial_quadrature R n Y NY hNY hY hSep
    S sv hS DS hDS s psi hPsiValue r hOff E ev hE D hD f g hConv K hFOff b hMass
    k alpha C qEta hQEta.
  exists d; split=>// mesh hMesh I A tag hPart x hx.
  exact:(@hBound I A tag mesh hPart hMesh x hx).
have[d [hd hUniform]]:=@finite_common_radius R (Finite.clone (symmetric_indices n k) _) R
  (fun mesh=>mesh) P hEach.
exists d; split=>// I A tag mesh hPart hMesh x hx.
pose W:=\sum_i fine (mu (A i))*:B (tag i) (ev f (tag i)).
pose err:=g-smooth_test_inclusion hE W.
have hCoefficients alpha:
    NY (@ez k (norm_multi_partial_arguments R alpha) (@D k x err))<=qEta*b.
  have hPartial:=@hUniform alpha mesh hMesh I A tag hPart x hx.
  have hSum:=@finite_kernel_test_sum_derivative_value R X Y N NY hN hNY
    S sv DS hDS L hL s psi hPsiValue E ev hE D hD B hB I tag
    (fun i=>fine (mu (A i))) (fun i=>ev f (tag i)) k x (norm_multi_partial_arguments R alpha).
  have hExact:@ez k (norm_multi_partial_arguments R alpha) (@D k x err)=
      @ez k (norm_multi_partial_arguments R alpha) (@D k x g)-
      \sum_i fine (mu (A i))*:
        ((@ep k (norm_multi_partial_arguments R alpha) (@DS k (x-tag i) s))*:ev f (tag i)).
    have hInner:@D k x err=@D k x g-@D k x (smooth_test_inclusion hE W).
      exact:(linearB (hom_as_linear (@D k x)) g (smooth_test_inclusion hE W)).
    have hOuter:@ez k (norm_multi_partial_arguments R alpha) (@D k x err)=
        @ez k (norm_multi_partial_arguments R alpha) (@D k x g)-
        @ez k (norm_multi_partial_arguments R alpha) (@D k x (smooth_test_inclusion hE W)).
      rewrite hInner.
      exact:(linearB (hom_as_linear (@ez k (norm_multi_partial_arguments R alpha)))
        (@D k x g) (@D k x (smooth_test_inclusion hE W))).
    by rewrite hOuter /W hSum.
  by rewrite hExact.
have hActual:=@smooth_derivative_exact R X Y N NY hN hNY (fun _=>True) E ev D hD k err x Logic.I.
have hNorm:=@hReconstruction (fun _=>True) (ev err) x (@D k x err) (qEta*b)
  (mulr_ge0 (ltW hQEta) hBMass) hActual hCoefficients.
have hCancel:M*qEta*(b+1)=eta by rewrite /qEta mulrAC mulrC divfK // gt_eqF.
have hMq:0<=M*qEta:=mulr_ge0 (ltW hM) (ltW hQEta).
have hBB:b<=b+1 by lra.
have hUpper:=ler_wpM2l hMq hBB; rewrite hCancel in hUpper.
apply:le_trans hNorm _.
by rewrite mulrA.
Qed.
End FiniteKernelTestSumJetApproximation.
