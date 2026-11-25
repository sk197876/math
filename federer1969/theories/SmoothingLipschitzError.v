(** Federer (1969), 4.1.14, p. 370: the smooth approximants
    can be constructed by smoothing f. This supporting quantitative
    estimate uses the positive unit-mass kernels of 4.1.2, pp. 346–347:
    smoothing a globally L-Lipschitz map at scale e changes its value
    by at most L e. No symmetry of the kernel is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothingDilationIntegral
  SmoothingConvolutionUP NormedSmoothingSubstitution
  ContinuousKernelConstantIntegral UnitKernelVectorDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_lipschitz_error_bound]: the uniform smoothing
    approximation invoked in Federer 4.1.14, p. 370, with its sharp
    Lipschitz scale. The norm may have any Banach target. A zero bound,
    a zero-dimensional source and a constant map are allowed. *)
Theorem smoothing_lipschitz_error_bound (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    e (f g:R_n R n->Y) L:
  0<e ->0<=L ->is_smoothing_convolution hNY (family e) f g ->
  (forall x y,NY (f x-f y)<=L*inner_norm (@euclidean_inner_productP R n) (x-y)) ->
  forall a,NY (g a-f a)<=L*e.
Proof.
move=>he hL hConvolution hBound a.
have hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hNonnegative:=@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he.
have hMass:=@smoothing_dilation_integral_one R n phi family hPhi hFamily e he.
have hIntegral:=@normed_smoothing_convolution_alternate_integral R n Y NY hNY
  (family e) f g hConvolution a.
have hConstant:=@continuous_kernel_constant_integral R n Y NY hNY hY
  (family e) e 1 (f a) hSmooth
  (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he) hMass.
rewrite scale1r in hConstant.
apply:(@unit_weight_vector_difference_bound R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (family e) (fun z=>f (a-z)) (fun _=>f a) (g a) (f a) (L*e)
  hNonnegative hMass hIntegral hConstant)=>z hNonzero.
have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he z hNonzero.
have hDifference:(a-z)-a = -z by rewrite addrAC subrr add0r.
have hLocal:=hBound (a-z) a.
rewrite hDifference (real_seminorm_negate
  (inner_norm_real_norm (@euclidean_inner_productP R n)).1) in hLocal.
exact:(le_trans hLocal (ler_wpM2l hL (ltW hRadius))).
Qed.
