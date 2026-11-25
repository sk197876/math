(** Federer (1969), 4.1.2, p. 347: compact
    smooth convolution of a continuous Banach-valued field
    exists without separability of the entire target.
    The actual range has the required separability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormClassOneUP NormRegularity
  NormClassZeroScalarProduct GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormEquivalence SmoothCompactSet PartialFunctionUP PartialFunctionBasic
  MeasureVectorIntegralUP EuclideanLebesgueDimensions SmoothingConvolutionUP
  SmoothScalarKernelTranslation ContinuousCompactFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ContinuousCompactConvolution.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable f:X->Y.
Hypothesis hF:norm_class_zero N NY (fun _=>True) f.
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall z,r<N z ->psi z=0.

(** Source for [continuous_compact_convolution_at_exists]:
    the multilinear-valued convolution in Federer 4.1.2,
    p. 347, has an actual integral at
    every point; only its continuous range is used. *)
Theorem continuous_compact_convolution_at_exists x:
  exists y:Y,is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(psi (x-z)*:f z:real_norm_metric_space hNY))) y.
Proof.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True) [set z|N (z-x)<=r]
  (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN x r).
have hProduct:=@norm_class_zero_scalar_product R X Y N NY hNY (fun _=>True)
  (fun z=>psi (x-z)) f (norm_class_continuous
    (@smooth_scalar_kernel_translation R n psi hPsi x 0%N)) hF.
apply:(@continuous_compact_field_integral_exists R n Y NY hNY hY _ K hProduct)=>z hz.
have hNo:~(N (z-x)<=r) by move=>hSmall; apply:hz.
have hLarge:r<N (x-z).
  rewrite (real_seminorm_subtract hN.1 x z) ltNge; exact/negP.
by rewrite (@hOff (x-z) hLarge) scale0r.
Qed.

(** Source for [continuous_compact_convolution_exists]:
    the actual Banach-valued integral fields in Federer
    4.1.2, p. 347, exist without a
    separability assumption on the full operator space. *)
Theorem continuous_compact_convolution_exists:
  exists g:X->Y,is_smoothing_convolution hNY psi f g.
Proof.
have[g hg]:=choice continuous_compact_convolution_at_exists.
exists g; exact hg.
Qed.
End ContinuousCompactConvolution.
