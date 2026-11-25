(** Federer (1969), 4.1.2, p. 347: for
    a class-one input, the directional derivative
    commutes with convolution by the original smoothing
    kernel. The alternate convolution formula and the
    compact-uniform quotient theorem give the printed calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity NormDifferentialUP NormedCurveDerivativeUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  MetricClosedBalls EuclideanNormClosedBalls NormCompactDirectionalQuotient EuclideanLebesgueDimensions
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius
  VectorDaniellHypotheses SmoothingConvolutionUP SmoothingConvolutionSubstitution
  MeasureVectorIntegralUP PartialFunctionBasic TotalVectorIntegralArithmetic UnitKernelVectorDifference EuclideanReflectionTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingInputQuotientIntegral.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.

Variables f g:X->Y.
Variable psi:X->R.
Hypothesis hConv:is_smoothing_convolution hNY psi f g.

(** Source for [smoothing_input_quotient_integral]: the actual
    integral of every input difference quotient equals the
    difference quotient of the convolution, supporting
    Federer 4.1.2, p. 347. No derivative is assumed here. *)
Theorem smoothing_input_quotient_integral (a v:X) (t:R):
  is_measure_vector_integral mu
    (partial_function_total (fun z=>(psi z*:(t^-1*:((f ((a-z)+t*:v))-f (a-z)))
      :real_norm_metric_space hNY))) (t^-1*:(g (a+t*:v)-g a)).
Proof.
have hAlternate:=@smoothing_convolution_alternate_integral R n Y NY hNY psi f g hSep hConv.
have hDiff:=@total_vector_integral_subtract R X Y NY hNY mu hm
  (fun z=>psi z*:f (a+t*:v-z)) (fun z=>psi z*:f (a-z))
  (g (a+t*:v)) (g a) (hAlternate (a+t*:v)) (hAlternate a).
have hScale:=@total_vector_integral_scale R X Y NY hNY mu hm
  (fun z=>psi z*:f (a+t*:v-z)-psi z*:f (a-z))
  (g (a+t*:v)-g a) t^-1 hDiff.
have hEq:(fun z:X=>(t^-1*:(psi z*:f (a+t*:v-z)-psi z*:f (a-z)):real_norm_metric_space hNY))=
    (fun z=>(psi z*:(t^-1*:(f ((a-z)+t*:v)-f (a-z))):real_norm_metric_space hNY)).
  apply:funext=>z; by rewrite addrAC -scalerBr !scalerA (mulrC t^-1 (psi z)).
by rewrite hEq in hScale.
Qed.
End SmoothingInputQuotientIntegral.
