(** Federer (1969), 4.1.2, p. 347: every
    originally defined Lebesgue point of a measurable
    partial field has the stated smoothing limit.
    The total-extension proof preserves both actual
    convolution integrals and that particular point value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  MetricClosedBalls PartialFunctionUP PartialFunctionBasic EuclideanLebesgueDimensions MeasureLebesgueSet
  LocallyIntegrablePartialFieldUP LocallyIntegrablePartialExtension PartialSmoothingConvolutionUP PartialConvolutionExtension
  SmoothingKernelUP SmoothingDilationUP SmoothingLebesguePoint LebesguePointExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [partial_smoothing_at_lebesgue_point]: the full
    original partial-function scope of the pointwise
    assertion in Federer 4.1.2, p. 347.
    No merely almost-everywhere substitute or added
    full-domain hypothesis replaces the printed Lebesgue set. *)
Theorem partial_smoothing_at_lebesgue_point (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (hSep:is_separable_normed_space hNY)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (f:partial_function (R_n R n) (real_norm_metric_space hNY))
    (g:R->R_n R n->Y):
  is_locally_integrable_partial_vector_field
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (@euclidean_lebesgue_measure R n) f ->
  (forall e:R,0<e ->is_partial_smoothing_convolution (family e) f (g e)) ->
  forall (V:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))->
      set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))->Prop)
    (a:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) (y:Y),
    (forall r:R,0<r ->V a (metric_closed_ball a r)) ->
    partial_function_graph f a y ->
    @measure_lebesgue_set R
      [the metricType R of real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))]
      [the metricType R of real_norm_metric_space hNY] (@euclidean_lebesgue_measure R n) V f a ->
    forall eta:R,0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->NY (g e a-y)<eta.
Proof.
move=>hField hConvolution V a y hBalls hy hLebesgue.
have [F [hExt [hAlmost hLocal]]]:=@locally_integrable_partial_total_extension R (R_n R n) Y
  (inner_norm (@euclidean_inner_productP R n)) NY (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) f hField.
have hFullConv e (he:0<e):
    SmoothingConvolutionUP.is_smoothing_convolution hNY (family e) F (g e).
  exact:(@partial_smoothing_convolution_extension_iff R n Y NY hNY (family e) f F (g e) hAlmost).1
    (@hConvolution e he).
have hFullLebesgue:=@lebesgue_point_total_extension R
  [the metricType R of real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))]
  [the metricType R of real_norm_metric_space hNY]
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) V f F hExt hAlmost a hLebesgue.
have hValue:F a=y:=@hExt a y hy.
have hLimit:=@smoothing_at_lebesgue_point R n Y NY hNY hSep phi hPhi family hFamily
  F hLocal g hFullConv V a hBalls hFullLebesgue.
by rewrite hValue in hLimit.
Qed.
