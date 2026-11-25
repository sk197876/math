(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: repeated
    kernel derivatives give all the original iterated
    derivatives of convolution. Every intermediate function
    is an actual convolution, and its derivative graph
    is the original recursive graph of 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity NormClassOneUP ContinuousFieldLocalIntegrability ContinuousCompactConvolution
  NormDifferentialUP NormDifferentialDirectional NormIteratedDirectionalUP NormIteratedDirectionalLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions
  LocallyIntegrableVectorFieldUP SmoothingConvolutionUP CompactScalarKernelDirectional
  CompactSmoothConvolutionExistence CompactSmoothConvolutionDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ContinuousConvolutionIteratedKernel.
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
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall z,r<N z ->psi z=0.
Variable g:X->Y.
Hypothesis hConvolution:is_smoothing_convolution hNY psi f g.

(** Source for [continuous_smooth_convolution_iterated_kernel]: the
    repeated original derivative computation yielding
    D^alpha(Phi*f)=(D^alpha Phi)*f in
    Federer 4.1.2, p. 347. The full
    recursive derivative domains are retained, including degree zero. *)
Theorem continuous_smooth_convolution_iterated_kernel (s:seq X):
  exists (theta:X->R) (q:X->Y),
    norm_class_all_orders hN hR (fun _=>True) theta /\
    (forall z,r<N z ->theta z=0) /\
    is_smoothing_convolution hNY theta f q /\
    (forall a,has_norm_iterated_directional (fun t:R^o=>`|t|) (fun _=>True) psi s a (theta a)) /\
    (forall a,has_norm_iterated_directional NY (fun _=>True) g s a (q a)).
Proof.
elim:s=>[|v s [theta [q [hTheta [hThetaOff [hQ [hIterTheta hIterQ]]]]]]].
- exists psi,g; split=>//; split=>//; split=>//; split; by move=>a; split.
- have [theta' [D [hTheta' [hTheta'Off [hD hDir]]]]]:=
    @compact_scalar_kernel_directional_exists R n theta r v hTheta hThetaOff.
  have [q' hQ']:=@continuous_compact_convolution_exists R n Y NY hNY hY f hContinuous
    theta' hTheta' r hTheta'Off.
  exists theta',q'; split=>//; split=>//; split=>//; split=>a.
  + exists theta; split.
    * move=>x y hy; exact:(@norm_iterated_directional_unique R X R^o (fun t:R^o=>`|t|)
        hR (fun _=>True) psi s x (theta x) y (hIterTheta x) hy).
    * split.
      - exists 1; split; first exact:ltr01.
        move=>t _; exists (theta (a+t*:v)); exact:hIterTheta.
      - rewrite -(hDir a).
        exact:(norm_differential_directional_limit hN hR (hD a) v).
  + exists q; split.
    * move=>x y hy; exact:(@norm_iterated_directional_unique R X Y NY hNY
        (fun _=>True) g s x (q x) y (hIterQ x) hy).
    * split.
      - exists 1; split; first exact:ltr01.
        move=>t _; exists (q (a+t*:v)); exact:hIterQ.
      - exact:(@compact_smooth_convolution_directional_derivative R n Y NY hNY
          f q q' theta theta' r hField hTheta hThetaOff hTheta'Off hQ hQ'
          v D hD hDir a).
Qed.
End ContinuousConvolutionIteratedKernel.
