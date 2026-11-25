(** Federer (1969), 4.1.18, p. 375: every
    original compact positive scalar test has a
    positive compact convolution for each positive
    scale. This is the fixed-scale version of the
    earlier compact smoothing law, without a small
    scale restriction on the full ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealMetricBackground RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormClassZeroWhole NormClassZeroTopology ScalarNormExtendedEmbedding
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CompactSupportFunctionUP FunctionLatticeUP CompactScalarVectorIdentification
  ScalarNormMetricCompleteness ContinuousFieldLocalIntegrability ContinuousCompactConvolution
  CompactSmoothConvolutionContinuity CompactConvolutionSupport
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP SmoothingNormMajorant EuclideanLebesgueDimensions
  VectorSetSum EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_compact_smoothing_exists]: the
    actual Phi_epsilon*f used in the averaged variation
    inequality of Federer 4.1.18, p. 375. Positivity,
    compact support and the literal convolution graph
    hold at every positive epsilon, including n= 0. *)
Theorem positive_compact_smoothing_exists (R:realType) n
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
    epsilon (hEpsilon:0<epsilon)
    (f:real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))->R^o):
  positive_function_lattice (@compactly_supported_continuous_functions R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) f ->
  exists g:R_n R n->R^o,
    positive_function_lattice (@compactly_supported_continuous_functions R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) g /\
    is_smoothing_convolution (@scalar_absolute_value_norm R) (family epsilon) f g.
Proof.
move=>hF.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT:=real_norm_metric_space hNX.
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
have hOwn:=(@compact_function_to_scalar_field R XT f hF.1).1.
have hClass:norm_class_zero NX NS (fun _=>True) f.
  exact:(@norm_continuous_whole_class_zero R X R^o NX NS hNX hNS f hOwn).
have hKernel:=@smoothing_dilation_smooth R n phi hPhi family hFamily epsilon hEpsilon.
have hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily epsilon hEpsilon.
have[g hConv]:=@continuous_compact_convolution_exists R n R^o NS hNS
  (@scalar_norm_metric_complete R) f hClass (family epsilon) hKernel epsilon hOff.
have hLocal:=@continuous_field_locally_norm_integrable R n R^o NS hNS f hClass.
have hGClass:=@compact_smooth_convolution_continuous R n R^o NS hNS f g
  (family epsilon) epsilon hLocal hKernel hOff hConv.
have hGContinuous:continuous (fun x:XT=>(g x:real_line_metric R)).
  move=>x;exact:(continuous_comp
    (@norm_class_zero_continuous_at R X R^o NX NS hNX hNS
      (fun _=>True) g x hGClass Logic.I)
    (@scalar_norm_real_identity_continuous R (g x))).
pose C:=@euclidean_closed_support_tube R n (real_function_support f) epsilon.
have hC:@compact XT C.
  exact:(@euclidean_closed_support_tube_norm_compact R n (real_function_support f) epsilon hF.1.2).
have hCClosed:@closed XT C:=compact_closed (@metric_hausdorff R XT) hC.
have hThick x z:real_function_support f z->NX (x-z)<=epsilon->C x.
  move=>hz hDistance.
  have h:=@vector_set_sum_contains X (real_function_support f)
    [set y|NX y<=epsilon] z (x-z) hz hDistance.
  by rewrite addrC subrK in h.
have hGOff:=@compact_convolution_support_bound R X R^o NX NS hNS
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (real_function_support f) C epsilon (family epsilon) f g
  hOff hThick (fun x hx=>@real_function_zero_off_support R XT f x hx) hConv.
exists g;split;last exact:hConv.
split.
- split;first exact:hGContinuous.
  exact:(@real_function_compact_support_in_closed_set R XT g C hC hCClosed hGOff).
- exact:(@smoothing_convolution_nonnegative R n (family epsilon) f g
    (@smoothing_dilation_nonnegative R n phi hPhi family hFamily epsilon hEpsilon)
    hConv hF.2).
Qed.
