(** Federer (1969), 4.1.18, p. 375: the
    norm of an original smoothed vector field is
    bounded by the corresponding positive scalar
    smoothing. This retains the exact coefficient one
    in the variation estimate.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanLebesgueDimensions PartialFunctionBasic MeasureVectorIntegralUP
  ScalarVectorIntegralIdentification TotalVectorIntegralEstimate SmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_convolution_norm_majorant]: the
    positive-kernel norm bound underlying the averaged
    variation inequality in Federer 4.1.18, p. 375.
    Both given convolutions have their original integral
    graphs; no additional summability premise is needed. *)
Theorem smoothing_convolution_norm_majorant (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (kernel:R_n R n->R) (f g:R_n R n->Y) (s t:R_n R n->R^o):
  (forall z,0<=kernel z) ->
  is_smoothing_convolution hNY kernel f g ->
  is_smoothing_convolution (@scalar_absolute_value_norm R) kernel s t ->
  (forall z,NY (f z)<=s z) ->forall x,NY (g x)<=t x.
Proof.
move=>hPositive hVector hScalar hBound x.
have hMajorant:=@scalar_vector_integral_identification R (R_n R n)
  (@euclidean_lebesgue_measure R n)
  (fun z=>kernel (x-z)*s z) (t x) (hScalar x).
apply:(@total_vector_integral_dominated_norm R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun z=>kernel (x-z)*:f z) (g x)
  (fun z=>kernel (x-z)*s z) (t x) (hVector x) hMajorant)=>z.
rewrite (real_seminorm_scale hNY.1) (ger0_norm (hPositive (x-z))).
apply:(ler_wpM2l (@hPositive (x-z))).
exact:(@hBound z).
Qed.

(** Source for [smoothing_convolution_nonnegative]: a
    positive compact scalar test has a positive
    smoothed majorant in the proof of 4.1.18,
    p. 375. This includes zero inputs and
    arbitrary nonsymmetric positive kernels. *)
Theorem smoothing_convolution_nonnegative (R:realType) n
    (kernel:R_n R n->R) (f g:R_n R n->R^o):
  (forall z,0<=kernel z) ->
  is_smoothing_convolution (@scalar_absolute_value_norm R) kernel f g ->
  (forall z,0<=f z) ->forall x,0<=g x.
Proof.
move=>hPositive hConv hF x.
have hBound:forall z,`|f z|<=f z.
  by move=>z;rewrite (ger0_norm (hF z)).
have h:=@smoothing_convolution_norm_majorant R n R^o
  (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R) kernel f g f g
  hPositive hConv hConv hBound x.
exact:le_trans (normr_ge0 (g x)) h.
Qed.
