(** Federer (1969), 4.1.2, p. 347: the
    actual smoothing convolution vanishes off the
    thickened original support. Its integral is
    proved zero there, including when the
    ambient Lebesgue measure is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions PartialFunctionBasic MeasureVectorIntegralUP MeasureVectorIntegralZero
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationNonzeroRadius SmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [compact_smoothing_support_bound]: the actual
    compact support of Phi_epsilon*f in the
    original test-function convergence assertion,
    Federer 4.1.2, p. 347. *)
Theorem compact_smoothing_support_bound (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (phi:R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (family:R->R_n R n->R)
    (hFamily:is_smoothing_dilation phi family)
    (K C:set (R_n R n)) r e (f g:R_n R n->Y):
  (forall x z,K z ->inner_norm (@euclidean_inner_productP R n) (x-z)<=r ->C x) ->
  0<e ->e<=r ->(forall z,~K z ->f z=0) ->
  is_smoothing_convolution hNY (family e) f g ->
  forall x,~C x ->g x=0.
Proof.
move=>hThick he her hOff hConv x hx.
have hZero:(fun z:R_n R n=>(family e (x-z)*:f z:real_norm_metric_space hNY))=
    (fun _=>(0:real_norm_metric_space hNY)).
  apply:funext=>z.
  case:(pselect (K z))=>hz.
  - have [hKernelZero|hKernelNonzero]:=eqVneq (family e (x-z)) 0.
    + by rewrite hKernelZero scale0r.
    + exfalso; apply:hx; apply:(@hThick x z hz).
      have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he (x-z) hKernelNonzero.
      exact:(le_trans (ltW hRadius) her).
  - by rewrite (@hOff z hz) scaler0.
have hIntegral:=hConv x; rewrite hZero in hIntegral.
exact:(measure_vector_integral_unique hIntegral
  (@measure_vector_integral_zero R (R_n R n) Y NY hNY (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n))).
Qed.
