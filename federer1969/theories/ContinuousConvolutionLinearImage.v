(** Federer (1969), 4.1.2, p. 347,
    used in 4.1.7, p. 358:
    bounded linear coefficient maps commute
    with convolution of continuous fields.
    Existence of the target integral follows
    from the original continuous compact-kernel
    integral, without whole-target separability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP NormClassOneUP
  NormClassZeroPostcompose NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct SmoothingConvolutionUP ContinuousCompactConvolution
  TotalVectorIntegralLinearImage EuclideanLebesgueDimensions MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ContinuousConvolutionLinearImage.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables Y Z:lmodType R.
Variables (NY:Y->R) (NZ:Z->R).
Hypotheses (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Hypothesis hZ:is_complete_metric_space (real_norm_metric_space hNZ).
Variables (f g:X->Y) (kernel:X->R) (radius:R).
Hypothesis hf:norm_class_zero NX NY (fun _=>True) f.
Hypothesis hKernel:norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) kernel.
Hypothesis hOff:forall z,radius<NX z->kernel z=0.
Variable L:Hom Y Z.
Hypothesis hL:norm_bounded_linear NY NZ L.

(** Source for [continuous_convolution_linear_image]:
    a bounded linear map commutes with
    the original compact-kernel convolution,
    supporting the exterior derivative approximation
    in Federer 4.1.7, p. 358,
    by the integral law of 2.4.12,
    pp. 87–88. *)
Theorem continuous_convolution_linear_image:
  is_smoothing_convolution hNY kernel f g->
  is_smoothing_convolution hNZ kernel (fun x=>L (f x)) (fun x=>L (g x)).
Proof.
move=>hConvolution x.
have hContinuous:=@norm_class_zero_postcompose R X Y Z NX NY NZ hNY
  (fun _=>True) f L hf hL.
have [value hIntegral]:=@continuous_compact_convolution_at_exists R n Z NZ hNZ hZ
  (fun z=>L (f z)) hContinuous kernel hKernel radius hOff x.
have hEqual:(fun z=>kernel (x-z)*:L (f z))=(fun z=>L (kernel (x-z)*:f z)).
  apply:funext=>z;by rewrite linearZ.
rewrite hEqual in hIntegral.
have hImage:=@total_vector_integral_linear_image R X Y Z NY NZ hNY hNZ
  (@euclidean_lebesgue_measure R n) L (fun z=>kernel (x-z)*:f z) (g x)
  hL hIntegral.1 (hConvolution x).
by rewrite -hEqual in hImage.
Qed.
End ContinuousConvolutionLinearImage.
