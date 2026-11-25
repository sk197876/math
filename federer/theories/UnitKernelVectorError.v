(** Federer (1969), 4.1.2, p. 347: the
    smoothing error is bounded by the weighted
    pointwise oscillation. The actual kernel has mass
    one, and its weighted constant integral is
    proved before subtracting it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground VectorDaniellHypotheses PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureVectorIntegralUP SummableRealFunctionUP SummableRealArithmetic
  WeightedConstantVectorIntegral TotalVectorIntegralArithmetic TotalVectorIntegralEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_weight_vector_error_bound]: the
    first smoothing error inequality of Federer 4.1.2,
    p. 347. An upper bound on
    the oscillation at every nonzero kernel value
    bounds the actual integral error by the same number. *)
Theorem unit_weight_vector_error_bound (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (w:X->R) (F:X->Y) (y a:Y) (e:R):
  is_separable_normed_space hN ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(w x:real_line_metric R))) ->
  (forall x,0<=w x) ->is_measure_integral mu (real_total_integrand w) (1:R)%:E ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(w x*:F x:real_norm_metric_space hN))) y ->
  (forall x,w x!=0 ->N (F x-a)<=e) ->N (y-a)<=e.
Proof.
move=>hSep hw hNonneg hMass hIntegral hOscillation.
have hConst:=@nonnegative_weighted_constant_vector_integral R X Y N hN mu hm w 1 a
  hSep hw hNonneg hMass.
rewrite scale1r in hConst.
have hError:=@total_vector_integral_subtract R X Y N hN mu hm
  (fun x=>w x*:F x) (fun x=>w x*:a) y a hIntegral hConst.
have hMajorant:=@real_total_integral_scale R X mu hm w 1 e hMass.
rewrite mulr1 in hMajorant.
apply:(@total_vector_integral_dominated_norm R X Y N hN mu hm
  (fun x=>w x*:F x-w x*:a) (y-a) (fun x=>e*w x) e hError hMajorant)=>x.
rewrite -scalerBr (real_seminorm_scale hN.1) (ger0_norm (hNonneg x)).
have [hZero|hNotZero]:=eqVneq (w x) 0.
- by rewrite hZero !mul0r mulr0.
- rewrite mulrC; exact:(ler_wpM2r (hNonneg x) (hOscillation x hNotZero)).
Qed.
