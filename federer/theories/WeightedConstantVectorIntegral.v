(** Federer (1969), 4.1.2, p. 347: a
    nonnegative scalar kernel of integral a times a
    fixed vector has vector integral a times that
    vector. The L1 condition is proved explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground VectorDaniellHypotheses PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasurableTotalBasic MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  SummableRealArithmetic MeasureVectorIntegralUP WeakDerivativeFieldVectorIntegral MeasurableScalarVectorProduct TotalVectorNormIntegrability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_weighted_constant_vector_integral]: the
    identity integral Phi_epsilon(z) y dz=y in
    the smoothing error display of Federer 4.1.2,
    p. 347, with arbitrary integral a included.
    The target need not be finite dimensional. *)
Theorem nonnegative_weighted_constant_vector_integral (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (w:X->R) a (y:Y):
  is_separable_normed_space hN ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(w x:real_line_metric R))) ->
  (forall x,0<=w x) ->is_measure_integral mu (real_total_integrand w) a%:E ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(w x*:y:real_norm_metric_space hN))) (a*:y).
Proof.
move=>hSep hw hNonneg hIntegral.
have hMeas:=@measurable_scalar_vector_product R X Y N hN mu hm w (fun _=>y) hSep hw
  (@measurable_total_constant R X (real_norm_metric_space hN) mu hm y).
have hNorm:is_measure_integral mu (real_total_integrand (fun x=>N (w x*:y))) (N y*a)%:E.
  have h:=@real_total_integral_scale R X mu hm w a (N y) hIntegral.
  have hEq:(fun x=>N y*w x)=(fun x=>N (w x*:y)).
    apply:funext=>x; by rewrite (real_seminorm_scale hN.1) (ger0_norm (hNonneg x)) mulrC.
  by rewrite hEq in h.
split.
- exact:(@total_vector_lone_from_norm_integral R X Y N hN mu hm _ (N y*a) hSep hMeas hNorm).
- move=>alpha hAlpha.
  have h:=@real_total_integral_scale R X mu hm w a (alpha y) hIntegral.
  have hValue:alpha (a*:y)=a*alpha y by rewrite linearZ.
  rewrite hValue (mulrC a (alpha y)).
  apply:(measure_integral_graph_equivalent _ h)=>x z.
  have hPoint:alpha (w x*:y)=w x*alpha y by rewrite linearZ.
  by rewrite total_functional_evaluation_graph real_total_integrand_graph hPoint mulrC.
Qed.
