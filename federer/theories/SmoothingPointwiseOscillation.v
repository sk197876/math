(** Federer (1969), 4.1.2, p. 347, used in
    4.1.12, p. 369: the original regularisation
    preserves a pointwise plateau and a scalar interval
    of values. Reuse the original positive unit kernel,
    actual constant integral and weighted difference estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP ScalarNormMetricCompleteness
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationIntegral
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP NormedSmoothingSubstitution
  ContinuousKernelConstantIntegral UnitKernelVectorDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingPointwiseOscillation.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variables (e:R) (f g:X->Y).
Hypothesis he:0<e.
Hypothesis hConvolution:is_smoothing_convolution hNY (family e) f g.

(** Source for [smoothing_pointwise_oscillation_bound]: the
    actual regularisation differs from a fixed vector a
    by at most the original input oscillation on the
    kernel support, by Federer 4.1.2, p. 347.
    This supports the exact test bounds in 4.1.12,
    p. 369, without separability of the full target. *)
Theorem smoothing_pointwise_oscillation_bound x a eta:
  (forall z,family e z!=0->NY (f (x-z)-a)<=eta)->NY (g x-a)<=eta.
Proof.
move=>hOscillation.
have hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hMass:=@smoothing_dilation_integral_one R n phi family hPhi hFamily e he.
have hConst:=@continuous_kernel_constant_integral R n Y NY hNY hY (family e) e 1 a
  hSmooth (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he) hMass.
rewrite scale1r in hConst.
exact:(@unit_weight_vector_difference_bound R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (family e) (fun z=>f (x-z)) (fun _=>a) (g x) a eta
  (@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he) hMass
  (@normed_smoothing_convolution_alternate_integral R n Y NY hNY (family e) f g hConvolution x)
  hConst hOscillation).
Qed.

(** Source for [smoothing_pointwise_plateau]: if the
    original input is identically a at every translate
    seen by the kernel, its actual regularisation has
    value a, supporting the unit plateau required in
    Federer 4.1.12, p. 369, by 4.1.2,
    p. 347. Kernel evenness is not assumed. *)
Theorem smoothing_pointwise_plateau x a:
  (forall z,family e z!=0->f (x-z)=a)->g x=a.
Proof.
move=>hOne.
have hBound:NY (g x-a)<=0.
  apply:(@smoothing_pointwise_oscillation_bound x a 0)=>z hz.
  by rewrite (hOne z hz) subrr (real_seminorm_zero hNY.1).
have hZero:NY (g x-a)=0 by apply/eqP;rewrite eq_le hBound (real_seminorm_nonnegative hNY.1).
exact:subr0_eq (hNY.2 _ hZero).
Qed.
End SmoothingPointwiseOscillation.

(** Source for [smoothing_scalar_unit_range]: positive
    normalized regularisation preserves values in [0,1],
    supporting the printed phi_k bounds of Federer
    4.1.12, p. 369, by 4.1.2, p. 347.
    The proof applies the original oscillation bound
    about 1/2 with radius 1/2. *)
Theorem smoothing_scalar_unit_range (R:realType) n (phi:R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (family:R->R_n R n->R)
    (hFamily:is_smoothing_dilation phi family) e (f g:R_n R n->R^o):
  0<e->is_smoothing_convolution (@scalar_absolute_value_norm R) (family e) f g->
  (forall x,0<=f x<=1)->forall x,0<=g x<=1.
Proof.
move=>he hConvolution hRange x.
have hBound:`|g x-1/2|<=1/2.
  apply:(@smoothing_pointwise_oscillation_bound R n R^o (fun t:R^o=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_norm_metric_complete R)
    phi hPhi family hFamily e f g he hConvolution x (1/2) (1/2))=>z _.
  have[h0 h1]:=andP (hRange (x-z)).
  rewrite ler_norml;apply/andP;split;lra.
rewrite ler_norml in hBound.
have[h0 h1]:=andP hBound;apply/andP;split;lra.
Qed.
