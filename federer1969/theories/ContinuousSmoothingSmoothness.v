(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: convolution
    with the original compact smooth kernel is smooth.
    The proof follows the printed coordinate-derivative
    iteration, reusing the previous differentiability and
    coordinate class theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormPartialDerivative NormRegularity NormClassOneUP ContinuousFieldLocalIntegrability ContinuousCompactConvolution
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions LocallyIntegrableVectorFieldUP SmoothingConvolutionUP
  CompactSmoothConvolutionExistence CompactSmoothConvolutionContinuity CompactSmoothConvolutionDirectional
  CompactScalarKernelDirectional CoordinateClassSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section ContinuousSmoothingSmoothness.
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
Hypothesis hContinuous:norm_class_zero N NY (fun _=>True) f.
(** Source for [hField]: continuous Euclidean fields have locally
    integrable norm, the original input condition of 4.1.2,
    p. 347, reused in Federer 4.1.3, p. 348. *)
Let hField:=@continuous_field_locally_norm_integrable R n Y NY hNY f hContinuous.

(** Source for [continuous_smooth_convolution_class]: every finite
    class follows by differentiating compact scalar kernels,
    Federer 4.1.2, p. 347. The actual continuous input range supplies essential
    separability; the full Banach target need not be separable. *)
Theorem continuous_smooth_convolution_class k:
  forall (psi:X->R) r (g:X->Y),
    norm_class_all_orders hN hR (fun _=>True) psi ->
    (forall z,r<N z ->psi z=0) ->
    is_smoothing_convolution hNY psi f g ->
    norm_class hN hNY (fun _=>True) g k.
Proof.
elim:k=>[|k IH] psi r g hPsi hOff hConvolution.
- apply:(@norm_class_zeroP R X Y N NY hN hNY (fun _=>True) g).2.
  exact:(@compact_smooth_convolution_continuous R n Y NY hNY f g psi r
    hField hPsi hOff hConvolution).
- have [theta hTheta]:=choice (fun i:'I_n=>
    @compact_scalar_kernel_directional_exists R n psi r (@coordinate_basis R n i) hPsi hOff).
  have [D hD]:=choice hTheta.
  have hExist i:exists q:X->Y,is_smoothing_convolution hNY (theta i) f q.
    exact:(@continuous_compact_convolution_exists R n Y NY hNY hY f hContinuous
      (theta i) (hD i).1 r (hD i).2.1).
  have [q hq]:=choice hExist.
  apply:(@norm_class_successor_coordinate_fields R n Y NY hNY g q k).
  + exact:(@compact_smooth_convolution_continuous R n Y NY hNY f g psi r
      hField hPsi hOff hConvolution).
  + move=>a i.
    exact:(@compact_smooth_convolution_directional_derivative R n Y NY hNY
      f g (q i) psi (theta i) r hField hPsi hOff (hD i).2.1 hConvolution (hq i)
      (@coordinate_basis R n i) (D i) (hD i).2.2.1 (hD i).2.2.2 a).
  + move=>i; exact:(IH (theta i) r (q i) (hD i).1 (hD i).2.1 (hq i)).
Qed.

(** Source for [continuous_smooth_convolution_smooth]: the original
    conclusion Phi_epsilon*f is of class infinity,
    Federer 4.1.2, p. 347, for the
    actual independently specified integral values. *)
Theorem continuous_smooth_convolution_smooth (psi:X->R) r (g:X->Y):
  norm_class_all_orders hN hR (fun _=>True) psi ->
  (forall z,r<N z ->psi z=0) ->
  is_smoothing_convolution hNY psi f g ->
  norm_class_all_orders hN hNY (fun _=>True) g.
Proof. move=>hPsi hOff hConv k; exact:(continuous_smooth_convolution_class k hPsi hOff hConv). Qed.
End ContinuousSmoothingSmoothness.
