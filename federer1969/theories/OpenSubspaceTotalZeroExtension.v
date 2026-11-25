(** Federer (1969), 4.1.18, p. 375: extend an
    original summable field by zero before ordinary
    convolution. Measurability and the literal scalar
    integral follow from 2.4.10 and 2.4.18 without
    continuity of the original field or an inhabited
    open subspace. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompactContinuousVectorZeroExtension
  OpenSubspaceExtension OpenSubspaceMeasure MeasureUP MeasureRestriction MeasurePushforward
  MeasureAlmostBasic PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  PartialZeroExtension PartialZeroExtensionLaws MeasurableFunctionUP MeasurableGraphEquivalence
  PushforwardMeasurableFunctions RestrictedFunctionMeasurability
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  RadonWeightedPushforwardIntegral RestrictedIntegralIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenSubspaceTotalZeroExtension.
Variable R:realType.
Variable X:pseudoMetricType R.
Variable U:set X.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hU:measure_measurable mu U.
Local Notation UT:=(set_type U).
Local Notation source:=(@open_subspace_measure R X U mu).
Local Notation hSource:=(@open_subspace_measure_is_measure R X U mu hm).

(** Source for [open_subspace_total_zero_extension_measurable]:
    a summable original-U field can be extended by
    zero as a measurable ambient field, supporting
    the convolution in Federer 4.1.18, p. 375,
    by the relative zero-extension law of 2.4.10. *)
Theorem open_subspace_total_zero_extension_measurable
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f:UT->real_norm_metric_space hNY):
  is_measure_measurable_function source (partial_function_total f) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x:X=>
      (@compact_vector_open_extension R X U Y f x:real_norm_metric_space hNY))).
Proof.
move=>hF.
pose g:=@compact_vector_open_extension R X U Y f.
have hPull:is_measure_measurable_function source
    (partial_function_precompose set_val
      (partial_function_total (fun x:X=>(g x:real_norm_metric_space hNY)))).
  apply:(@measurable_function_graph_equivalent R UT (real_norm_metric_space hNY)
    source _ _ _ hF)=>x y.
  change (f x=y<->g (set_val x)=y).
  by rewrite /g compact_vector_open_extension_value.
have hImage:=@pushforward_function_measurable_from_composition R UT X
  (real_norm_metric_space hNY) source set_val _ hPull.
rewrite open_subspace_measure_pushforward in hImage.
have hZero:=@restricted_measurable_zero_extension R X (real_norm_metric_space hNY)
  mu hm 0 U _ hU hImage.
apply:(@measurable_function_graph_equivalent R X (real_norm_metric_space hNY)
  mu _ _ _ hZero)=>x y.
case:(pselect (U x))=>hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx).
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (y=0<->g x=y).
  rewrite /g (compact_vector_open_extension_outside _ hx).
  by split=>->.
Qed.

(** Source for [open_subspace_total_zero_extension_integral]:
    the literal original-U scalar integral equals
    the ambient integral of its total zero extension,
    supporting Federer 4.1.18, pp. 375–377. Signed
    and infinite integral values retain their original
    definedness; no point of U is selected. *)
Theorem open_subspace_total_zero_extension_integral (f:UT->R) a:
  is_measure_integral source (real_total_integrand f) a ->
  is_measure_integral mu (real_total_integrand (@open_extension R X U f)) a.
Proof.
move=>hF.
pose g:=@open_extension R X U f.
have hPull:is_measure_integral source
    (real_total_integrand (fun x:UT=>g (set_val x))) a.
  have hEqual:(fun x:UT=>g (set_val x))=f.
    apply:funext=>x;exact:open_extensionE.
  by rewrite hEqual.
have hImage:=(@real_total_pushforward_integral_iff R UT X source hSource
  set_val g hPull.1 a).1 hPull.
rewrite open_subspace_measure_pushforward in hImage.
have hZero:=(@restricted_integral_zero_extension_iff R X mu hm U
  (real_total_integrand g) a hU).1 hImage.
apply:(@measure_integral_graph_equivalent R X mu _ _ a _ hZero)=>x y.
case:(pselect (U x))=>hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx).
- rewrite (partial_function_zero_extension_off _ _ _ hx) real_total_integrand_graph.
  rewrite /g (open_extension_out _ hx).
  change (y=0%E<->0%E=y);by split=>->.
Qed.
End OpenSubspaceTotalZeroExtension.
