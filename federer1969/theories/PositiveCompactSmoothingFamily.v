(** Federer (1969), 4.1.18, p. 375: positive
    compact scalar tests have actual positive compact
    convolutions, one common compact support and uniform
    convergence. All data follow from the preceding
    original compact smoothing theorem.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CompactSupportFunctionUP CompactScalarVectorIdentification CompactContinuousDomainFields
  SmoothFunctionSpaceSealed SmoothTestSpaces SmoothTestEvaluation SmoothTestCompactContinuous
  ScalarNormMetricCompleteness SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingConvolutionUP CompactUniformApproximationUP
  CompactContinuousConvolutionApproximation SmoothingNormMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_compact_smoothing_family_exists]:
    the original smoothed compact positive tests in
    the weak variation proof, Federer 4.1.18,
    p. 375. The full ambient measure may
    be infinite, and the kernel need not be even. *)
Theorem positive_compact_smoothing_family_exists (R:realType) n
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
    (f:real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))->R^o):
  compactly_supported_continuous_functions f ->(forall x,0<=f x) ->
  exists (g:R->R_n R n->R^o) (C:set (R_n R n)) (r:R),
    @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) C /\0<r /\
    (forall epsilon:R,0<epsilon ->epsilon<r ->
      @compactly_supported_continuous_functions R
        (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
        (g epsilon) /\
      (forall x,0<=g epsilon x) /\
      is_smoothing_convolution (@scalar_absolute_value_norm R) (family epsilon)
        f (g epsilon) /\(forall x,~C x->g epsilon x=0)) /\
    forall eta:R,0<eta ->exists d:R,0<d /\
      forall epsilon:R,0<epsilon ->epsilon<r ->epsilon<d ->
        forall x,`|g epsilon x-f x|<eta.
Proof.
move=>hF hFPositive.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior NX x.
pose E:=@SmoothFunctionSpace.space R X R^o NX NS hNX hNS Full hFull.
pose ev:=@SmoothFunctionSpace.value R X R^o NX NS hNX hNS Full hFull.
pose hE:=@SmoothFunctionSpace.laws R X R^o NX NS hNX hNS Full hFull.
have hDomain:@compact_continuous_domain_fields R (real_norm_metric_space hNX)
    Full R^o NS hNS f.
  split;first exact:compact_function_to_scalar_field hF.
  by move=>x _.
have [P [hApprox [r [hr hConv]]]]:=
  @compact_continuous_convolution_test_approximation R n R^o NS hNS
    (@scalar_norm_metric_complete R) Full hFull E ev hE phi hPhi family hFamily f hDomain.
have [C [hC [hCFull [r0 [hr0 [hOff hUniform]]]]]]:=hApprox.
pose g epsilon:=smooth_test_value hE (P epsilon).
exists g,C,(Order.min r r0);split;first exact:hC.
split;first by rewrite lt_min hr hr0.
split.
- move=>epsilon he heSmall.
  have hR:Order.min r r0<=r by rewrite ge_min lexx.
  have hR0:Order.min r r0<=r0 by rewrite ge_min lexx orbT.
  have hConvolution:=hConv epsilon he (lt_le_trans heSmall hR).
  split.
  + apply:compact_scalar_field_to_function.
    exact:(@smooth_test_compact_continuous_field R X R^o NX NS hNX hNS
      Full E ev hE (P epsilon)).1.
  + split.
    * exact:(@smoothing_convolution_nonnegative R n (family epsilon) f (g epsilon)
        (@smoothing_dilation_nonnegative R n phi hPhi family hFamily epsilon he)
        hConvolution hFPositive).
    * split;first exact:hConvolution.
      exact:hOff epsilon he (lt_le_trans heSmall hR0).
- move=>eta hEta;have [d [hd hSmall]]:=hUniform eta hEta.
  exists d;split=>// epsilon he _ hed x.
  exact:hSmall epsilon he hed x.
Qed.
