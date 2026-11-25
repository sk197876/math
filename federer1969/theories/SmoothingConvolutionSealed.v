(** Federer (1969), 4.1.2, p. 347: opaque
    actual convolution with the original positive-scale kernel.
    The vector integral specification precedes its existence;
    consumers use only the resulting integral law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions LocallyIntegrableVectorFieldUP
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP SmoothingConvolutionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SmoothingConvolutionSignature.
(** Source for [value]: the original actual
    Phi_epsilon*f, Federer 4.1.2, p. 347. *)
Parameter value:forall (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (e:R) (he:0<e) (f:R_n R n->Y)
    (hField:@is_locally_integrable_vector_field R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
      (@euclidean_lebesgue_measure R n) f),R_n R n->Y.
(** Source for [laws]: every value is the
    prescribed Banach-valued kernel integral,
    Federer 4.1.2, p. 347. *)
Parameter laws:forall (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (e:R) (he:0<e) (f:R_n R n->Y)
    (hField:@is_locally_integrable_vector_field R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
      (@euclidean_lebesgue_measure R n) f),
  @is_smoothing_convolution R n Y NY hNY (family e) f (@value R n Y NY hNY hY hSep phi hPhi family hFamily e he f hField).
End SmoothingConvolutionSignature.
Module SmoothingConvolution:SmoothingConvolutionSignature.
(** Source for [value]: select the already
    proved convolution witness, Federer 4.1.2, p. 347. *)
Definition value (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (e:R) (he:0<e) (f:R_n R n->Y)
    (hField:@is_locally_integrable_vector_field R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
      (@euclidean_lebesgue_measure R n) f):R_n R n->Y:=
  projT1 (cid (@smoothing_convolution_exists R n Y NY hNY hY hSep phi hPhi family hFamily e he f hField)).
(** Source for [laws]: the hidden witness satisfies
    the independently stated integral values,
    Federer 4.1.2, p. 347. *)
Lemma laws (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (hSep:is_separable_normed_space hNY)
    (phi:R_n R n->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R n->R) (hFamily:is_smoothing_dilation phi family)
    (e:R) (he:0<e) (f:R_n R n->Y)
    (hField:@is_locally_integrable_vector_field R (R_n R n) Y
      (inner_norm (@euclidean_inner_productP R n)) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
      (@euclidean_lebesgue_measure R n) f):
  @is_smoothing_convolution R n Y NY hNY (family e) f (@value R n Y NY hNY hY hSep phi hPhi family hFamily e he f hField).
Proof. exact:(projT2 (cid (@smoothing_convolution_exists R n Y NY hNY hY hSep phi hPhi family hFamily e he f hField))). Qed.
End SmoothingConvolution.
