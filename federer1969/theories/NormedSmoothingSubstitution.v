(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: both
    original convolution integrals agree. The substitution
    z |-> x-z is an actual involutive Lebesgue
    isometry in every dimension, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses PartialFunctionBasic
  MeasureVectorIntegralUP MeasureVectorIntegralAlmostEquality MeasureAlmostBasic GrassmannAbbreviations
  EuclideanLebesgueDimensions SmoothingConvolutionUP EuclideanReflectionTranslation NormedInvariantVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [normed_smoothing_convolution_alternate_integral]: the
    second original formula for Phi*f in Federer
    4.1.2, p. 347, with its full
    Banach-valued integral domain retained. *)
Theorem normed_smoothing_convolution_alternate_integral (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (psi:R_n R n->R) (f g:R_n R n->Y):
  is_smoothing_convolution hNY psi f g ->
  forall x,is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(psi z*:f (x-z):real_norm_metric_space hNY))) (g x).
Proof.
move=>hConvolution x.
have hInv:=@euclidean_reflection_translation_involutive R n x.
have hIntegral:=@normed_invariant_total_vector_integral R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun z=>x-z) (fun z=>psi (x-z)*:f z) (g x)
  (can_inj hInv) (@euclidean_reflection_translation_measure R n x) (hConvolution x).
have hEq:(fun z:R_n R n=>(psi (x-(x-z))*:f (x-z):real_norm_metric_space hNY))=
    (fun z=>(psi z*:f (x-z):real_norm_metric_space hNY)).
  apply:funext=>z; by rewrite hInv.
by rewrite hEq in hIntegral.
Qed.
