(** Federer (1969), 4.1.2, p. 347: the
    original partial-field convolution exists and is smooth.
    A measurable total extension proves existence, and
    almost-everywhere invariance restores the original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions
  LocallyIntegrablePartialFieldUP LocallyIntegrablePartialExtension PartialSmoothingConvolutionUP
  PartialConvolutionExtension CompactSmoothConvolutionExistence CompactSmoothConvolutionSmoothness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [partial_compact_smooth_convolution_exists]: the
    full measurable-function scope of the first smoothing
    assertion in Federer 4.1.2, p. 347.
    No total-domain hypothesis is added; each value
    is an actual Banach integral of the original partial field. *)
Theorem partial_compact_smooth_convolution_exists (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (f:partial_function (R_n R n) (real_norm_metric_space hNY)) (psi:R_n R n->R) r:
  is_locally_integrable_partial_vector_field
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (@euclidean_lebesgue_measure R n) f ->
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) (fun _=>True) psi ->
  (forall z,r<inner_norm (@euclidean_inner_productP R n) z ->psi z=0) ->
  exists g:R_n R n->Y,is_partial_smoothing_convolution psi f g /\
    norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY (fun _=>True) g.
Proof.
move=>hField hPsi hOff.
have [F [hExt [hAlmost hLocal]]]:=@locally_integrable_partial_total_extension R (R_n R n) Y
  (inner_norm (@euclidean_inner_productP R n)) NY (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) f hField.
have [g hg]:=@compact_smooth_convolution_exists R n Y NY hNY hY hSep F hLocal psi hPsi r hOff.
exists g; split.
- exact:(@partial_smoothing_convolution_extension_iff R n Y NY hNY psi f F g hAlmost).2 hg.
- exact:(@compact_smooth_convolution_smooth R n Y NY hNY hY hSep F hLocal psi r g hPsi hOff hg).
Qed.
