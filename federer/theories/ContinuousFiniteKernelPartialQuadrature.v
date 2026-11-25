(** Federer (1969), 4.1.3, p. 348, reusing 4.1.2:  the
    original multiindex derivative of the convolution is
    approximated, uniformly on compact sets, by the
    differentiated tagged Borel sum. The integral and
    every partial derivative are the actual proved ones. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearSealed NormHigherMultiPartialUP PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothSmoothingPartials
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext TopologicalBorel
  ContinuousFieldLocalIntegrability LocallyIntegrableVectorFieldUP SmoothingConvolutionUP ContinuousConvolutionMultiPartial
  FiniteTaggedBorelPartitionUP FiniteTaggedVectorIntegral CompactKernelFieldOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ContinuousFiniteKernelPartialQuadrature.
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

(** Source for [continuous_finite_kernel_partial_quadrature]: the original
    compact-uniform D^alpha approximation in Federer 4.1.2,
    p. 348, with an actual finite
    integral error bound and the exact original cell masses. *)
Theorem continuous_finite_kernel_partial_quadrature k (alpha:symmetric_indices n k)
    (C:smooth_compact_set hN (fun _=>True)) (eta:R):
  0<eta ->exists d:R,0<d /\ forall (I:finType) (A:I->set X) (tag:I->X) (mesh:R),
    @is_finite_tagged_borel_partition R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag ->mesh<d ->
    forall x,smooth_compact_carrier C x ->
      NY (@ez k (norm_multi_partial_arguments R alpha) (@D k x g)-
        \sum_i fine (mu (A i))*:
          ((@ep k (norm_multi_partial_arguments R alpha) (@DS k (x-tag i) s))*:ev f (tag i)))<=eta*b.
Proof.
move=>hEta.
pose theta x:=@ep k (norm_multi_partial_arguments R alpha) (@DS k x s).
pose q x:=@ez k (norm_multi_partial_arguments R alpha) (@D k x g).
have hFunction:sv s=psi by apply:funext=>x; exact:hPsiValue.
have hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
  rewrite -hFunction; exact:smooth_function_evaluation_smooth hS s.
have hTheta a:has_norm_multi_partial N ep PN (fun _=>True) psi alpha a (theta a).
  exists (@DS k a s); split; last reflexivity.
  have h:=@smooth_derivative_exact R X R^o N NS hN hNS (fun _=>True) S sv DS hDS k s a Logic.I.
  by rewrite hFunction in h.
have hQ a:has_norm_multi_partial N ez ZN (fun _=>True) (ev g) alpha a (q a).
  exists (@D k a g); split; last reflexivity.
  exact:(@smooth_derivative_exact R X Y N NY hN hNY (fun _=>True) E ev D hD k g a Logic.I).
have hFCont:=norm_class_continuous (smooth_function_evaluation_smooth hE f 0%N).
have hLocal:=@continuous_field_locally_norm_integrable R n Y NY hNY (ev f) hFCont.
have hIntegral:=@continuous_convolution_multi_partial_kernel R n Y NY hNY hY (ev f) hFCont
  psi hPsi r hOff (ev g) hConv k alpha theta q hTheta hQ.
have hThetaCont:=@smooth_multi_partial_field_continuous R n R^o NS hNS S sv hS DS hDS k alpha s.
have[d [hd hUniform]]:=@compact_kernel_field_oscillation R X Y N NY hN hNY
  (smooth_compact_carrier C) (smooth_compact_carrier K) theta (ev f)
  (smooth_compact_is_compact C) (smooth_compact_is_compact K) hThetaCont hFCont eta hEta.
exists d; split=>// I A tag mesh hPart hMesh x hx.
have hKMeas:=@euclidean_distribution_measure_borel R n (smooth_compact_carrier K)
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hN))
    (smooth_compact_is_compact K))).
have hAMeas i:=@euclidean_distribution_measure_borel R n (A i)
  (@finite_tagged_partition_borel R (real_norm_metric_space hN) (smooth_compact_carrier K)
    mesh I A tag hPart i).
apply:(@finite_tagged_vector_quadrature_bound R (real_norm_metric_space hN) Y NY hNY mu hm
  (smooth_compact_carrier K) b hMass hKMeas mesh I A tag hPart hAMeas
  (fun z=>theta (x-z)*:ev f z) (q x) eta (hIntegral x)).
- move=>z hz; by rewrite (@hFOff z hz) scaler0.
- move=>i z hz; apply:ltW; apply:(@hUniform x z (tag i) hx).
  + exact:(@finite_tagged_partition_inside R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag hPart i z hz).
  + apply:(@finite_tagged_partition_inside R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag hPart i).
    apply:(@finite_tagged_partition_tag R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag hPart i); by exists z.
  + have hBound:=@finite_tagged_partition_mesh R (real_norm_metric_space hN)
      (smooth_compact_carrier K) mesh I A tag hPart i z hz.
    exact:le_lt_trans hBound hMesh.
Qed.
End ContinuousFiniteKernelPartialQuadrature.
