(** Federer (1969), 4.1.18, p. 374: the
    literal reflected-kernel translation average is the
    original convolution. Lebesgue reflection is proved
    earlier; no evenness assumption on Phi is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  MeasureVectorIntegralUP GrassmannAbbreviations EuclideanLebesgueDimensions
  EuclideanReflectionTranslation NormedInvariantVectorIntegral
  SmoothingConvolutionUP NormedSmoothingSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_reflected_translation_integral]:
    the first displayed Phi_epsilon*phi integral in
    Federer 4.1.18, p. 374. The earlier
    normed integral substitution retains the whole
    original graph and needs no separability premise. *)
Theorem smoothing_reflected_translation_integral (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (kernel:R_n R n->R) (f g:R_n R n->Y):
  is_smoothing_convolution hNY kernel f g ->forall x,
    is_measure_vector_integral (@euclidean_lebesgue_measure R n)
      (partial_function_total (fun z=>
        (kernel (-z)*:f (x+z):real_norm_metric_space hNY))) (g x).
Proof.
move=>hConvolution x.
have hOriginal:=@normed_smoothing_convolution_alternate_integral R n Y NY hNY
  kernel f g hConvolution x.
have hNeg:injective (fun z:R_n R n=>-z).
  by move=>z y h;rewrite -(opprK z) -(opprK y) h.
have hMeasure:=@euclidean_reflection_translation_measure R n 0.
have hFunction:(fun z:R_n R n=>0-z)=(fun z=>-z).
  by apply:funext=>z;rewrite sub0r.
rewrite hFunction in hMeasure.
have hIntegral:=@normed_invariant_total_vector_integral R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun z=>-z) (fun z=>kernel z*:f (x-z)) (g x)
  hNeg hMeasure hOriginal.
have hIntegrand:(fun z:R_n R n=>
    (kernel (-z)*:f (x-(-z)):real_norm_metric_space hNY))=
    (fun z=>(kernel (-z)*:f (x+z):real_norm_metric_space hNY)).
  by apply:funext=>z;rewrite opprK.
by rewrite hIntegrand in hIntegral.
Qed.
