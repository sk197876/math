(** Federer (1969), 4.1.2, p. 347: an
    integrable scalar bound gives the actual Banach-valued
    kernel integral and its norm estimate. The proof
    uses the original vector-integral specification and
    the earlier scalar domination theorem of 2.4.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness SummableRealFunctionUP
  VectorDaniellPairingMeasurability MeasureLoneNormIntegralGeneral MeasureLpNorm
  MeasureVectorIntegralUP MeasureVectorIntegralSealed MeasureVectorIntegralBound TotalVectorNormIntegrability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [total_vector_lone_norm_value]: the original
    L1 norm equals the finite actual norm integral,
    supporting Federer 4.1.2, p. 347, by
    the proved formula of 2.4.12, p. 86. *)
Theorem total_vector_lone_norm_value (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y) b:
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) ->
  is_measure_integral mu (real_total_integrand (fun x=>N (f x))) b%:E ->
  measure_lp_norm mu N 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))=b%:E.
Proof.
move=>hf hIntegral.
have hNorm:=@measurable_lone_norm_integral R X Y N hN mu hm _ hf.
have hValue:is_measure_integral mu (real_total_integrand (fun x=>N (f x)))
    (measure_lp_norm mu N 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))).
  apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hNorm).
  move=>x y; exact:(@total_vector_norm_power_one_graph R X Y N hN f x y).
exact:measure_integral_unique hValue hIntegral.
Qed.

(** Source for [dominated_total_vector_integral_exists]: the
    actual kernel integrand has a Banach-valued integral
    bounded by its finite scalar majorant, supporting
    Federer 4.1.2, p. 347. The
    ambient measure need not have finite mass. *)
Theorem dominated_total_vector_integral_exists (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N)
    (hY:is_complete_metric_space (real_norm_metric_space hN))
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y) (g:X->R) b:
  is_separable_normed_space hN ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  (forall x,N (f x)<=g x) ->
  exists y:Y,is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y /\ N y<=b.
Proof.
move=>hSep hf hg hBound.
have hMeas:=@total_vector_norm_integrand_measurable R X Y N hN mu hm f hf.
have hDom x:`|N (f x)|<=g x.
  rewrite (ger0_norm (real_seminorm_nonnegative hN.1 (f x))); exact:hBound.
have [a [hNorm hA]]:=real_total_dominated_integral hm hMeas hg hDom.
have hLone:=@total_vector_lone_from_norm_integral R X Y N hN mu hm f a hSep hf hNorm.
pose y:=@MeasureVectorIntegral.value R X Y N hN hY mu hm _ hLone.
have hIntegral:=@MeasureVectorIntegral.laws R X Y N hN hY mu hm _ hLone.
have hNormValue:=@total_vector_lone_norm_value R X Y N hN mu hm f a hf hNorm.
have hUpper:=@measure_vector_integral_norm_bound R X Y N hN mu hm _ y hIntegral.
rewrite hNormValue lee_fin in hUpper.
exists y; split; first exact hIntegral.
exact:(le_trans hUpper (le_trans (ler_norm a) hA)).
Qed.
