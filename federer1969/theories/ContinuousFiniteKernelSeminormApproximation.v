(** Federer (1969), 4.1.3, p. 348, reusing 4.1.2:  the
    actual finite Borel sums approach the convolution
    in every original derivative seminorm. One mesh
    controls all derivative orders used by the distribution
    continuity bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearSealed NormHigherMultiPartialUP PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP MeasureUP
  FiniteCommonRadius HigherDifferentialFinitePartialBound SmoothGlobalTranslationUP
  TranslatedKernelTestUP ContinuousFiniteKernelPartialQuadrature FiniteKernelTestSumDerivative ContinuousFiniteKernelJetApproximation
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothCompactSet SmoothTestSpaces SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothSmoothingPartials
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext TopologicalBorel
  ContinuousFieldLocalIntegrability LocallyIntegrableVectorFieldUP SmoothingConvolutionUP ContinuousConvolutionMultiPartial
  FiniteTaggedBorelPartitionUP FiniteTaggedVectorIntegral CompactKernelFieldOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ContinuousFiniteKernelSeminormApproximation.
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


(** Source for [continuous_finite_kernel_seminorm_approximation]: the
    precise original seminorm form of the uniform
    approximation in Federer 4.1.2, p. 348.
    The finite sum is an actual test function. *)
Theorem continuous_finite_kernel_seminorm_approximation i
    (C:smooth_compact_set hN (fun _=>True)) (eta:R):
  0<eta ->exists d:R,0<d /\ forall (I:finType) (A:I->set X) (tag:I->X) (mesh:R),
    @is_finite_tagged_borel_partition R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag ->mesh<d ->
    smooth_function_derivative_seminorm hD C i
      (g-smooth_test_inclusion hE (\sum_j fine (mu (A j))*:B (tag j) (ev f (tag j))))<eta.
Proof.
move=>hEta; have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
have hEach j:=@continuous_finite_kernel_jet_approximation R n Y NY hNY hY S sv hS DS hDS
  s psi hPsiValue r hOff E ev hE D hD f g hConv K hFOff b hMass L hL B hB j C (eta/2) hHalf.
have hThrough m:exists d:R,0<d /\ forall (I:finType) (A:I->set X) (tag:I->X) (mesh:R),
    @is_finite_tagged_borel_partition R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag ->mesh<d ->
    forall j,(j<=m)%N ->forall x,smooth_compact_carrier C x ->
      @ZN j (@D j x (g-smooth_test_inclusion hE
        (\sum_l fine (mu (A l))*:B (tag l) (ev f (tag l)))))<=eta/2.
  elim:m=>[|m [d [hd hb]]].
  - have[d [hd hb]]:=hEach 0%N.
    exists d; split=>// I A tag mesh hPart hMesh j; rewrite leqn0=>/eqP ->.
    exact:(@hb I A tag mesh hPart hMesh).
  - have[t [ht hLast]]:=hEach m.+1.
    exists (Num.min d t); split; first by rewrite lt_min hd ht.
    move=>I A tag mesh hPart; rewrite lt_min=>/andP [hmd hmt] j hj.
    case:(eqVneq j m.+1)=>[->|hNe]; first exact:(@hLast I A tag mesh hPart hmt).
    have hjm:(j<=m)%N by move:hj; rewrite leq_eqVlt (negPf hNe) /= ltnS.
    exact:(@hb I A tag mesh hPart hmd j hjm).
have[d [hd hb]]:=hThrough i.
exists d; split=>// I A tag mesh hPart hMesh.
pose err:=g-smooth_test_inclusion hE (\sum_j fine (mu (A j))*:B (tag j) (ev f (tag j))).
have hBound:smooth_function_derivative_seminorm hD C i err<=eta/2.
  apply:(@smooth_derivative_seminorm_least R X Y N NY hN hNY (fun _=>True) E D C i
    (smooth_function_derivative_seminorm hD C i) (smooth_function_derivative_seminorm_laws hD C i)
    err (eta/2) (ltW hHalf))=>j hj x hx.
  exact:(@hb I A tag mesh hPart hMesh j hj x hx).
apply:le_lt_trans hBound _; lra.
Qed.
End ContinuousFiniteKernelSeminormApproximation.
