(** Federer (1969), 4.1.2, pp. 347-348:
    the actual convolution of a compactly supported
    field vanishes outside the thickened original compact.
    Integral uniqueness proves the support bound directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureVectorIntegralUP MeasureVectorIntegralZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [compact_convolution_support_bound]: the common
    compact support of the original smoothing and finite
    approximations in Federer 4.1.2, pp. 347-348.
    No positivity or unit-mass condition on the auxiliary
    kernel is needed for this support assertion. *)
Theorem compact_convolution_support_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu)
    (K C:X->Prop) r (psi:X->R) (f g:X->Y):
  (forall z,r<NX z ->psi z=0) ->
  (forall x z,K z ->NX (x-z)<=r ->C x) ->
  (forall z,~K z ->f z=0) ->
  (forall x,is_measure_vector_integral mu
    (partial_function_total (fun z=>(psi (x-z)*:f z:real_norm_metric_space hNY))) (g x)) ->
  forall x,~C x ->g x=0.
Proof.
move=>hOff hThick hFOff hIntegral x hx.
have hZero:(fun z:X=>(psi (x-z)*:f z:real_norm_metric_space hNY))=
    (fun _ : X=>(0:real_norm_metric_space hNY)).
  apply:funext=>z; case:(pselect (K z))=>hz.
  - have hLarge:r<NX (x-z).
      rewrite ltNge; apply/negP=>hSmall; apply:hx; exact:(@hThick x z hz hSmall).
    by rewrite (@hOff (x-z) hLarge) scale0r.
  - by rewrite (@hFOff z hz) scaler0.
have h:=hIntegral x; rewrite hZero in h.
exact:(measure_vector_integral_unique h (@measure_vector_integral_zero R X Y NY hNY mu hm)).
Qed.
