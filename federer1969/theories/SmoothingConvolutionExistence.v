(** Federer (1969), 4.1.2, p. 347: every
    positive original kernel dilation has an actual
    Banach-valued convolution with the given locally
    norm-integrable field. The previously proved kernel
    laws discharge the compact support and smoothness premises. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness CompactSupportFunctionUP EuclideanLebesgueDimensions
  LocallyIntegrableVectorFieldUP SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationSupport
  SmoothingConvolutionUP CompactSmoothConvolutionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_convolution_exists]: the actual
    convolution Phi_epsilon*f exists at every point
    for every positive epsilon, Federer 4.1.2,
    p. 347. The target remains an
    arbitrary separable Banach space. *)
Theorem smoothing_convolution_exists (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (e:R) (he:0<e) (f:R_n R n->Y)
    (hField:@is_locally_integrable_vector_field R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
      (@euclidean_lebesgue_measure R n) f):
  exists g:R_n R n->Y,is_smoothing_convolution hNY (family e) f g.
Proof.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hSupport:=@smoothing_dilation_support_radius R n phi hPhi family hFamily e he.
have hOff z:e<N z ->family e z=0.
  move=>hLarge; apply:(@real_function_zero_off_support R (real_norm_metric_space hN) (family e) z).
  move=>hs; have hSmall:N z<e:=hSupport z hs.
  by move:hSmall; rewrite ltNge (ltW hLarge).
exact:(@compact_smooth_convolution_exists R n Y NY hNY hY hSep f hField (family e) hSmooth e hOff).
Qed.
