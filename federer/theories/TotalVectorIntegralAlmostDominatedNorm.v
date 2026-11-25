(** Federer (1969), 4.1.14, p. 371: integrate the original
    almost-everywhere derivative bound after smoothing. This supporting
    norm estimate reuses the vector integral bound of 2.4.12,
    pp. 87–88, and invariance under null modifications in 2.3.1,
    p. 72. No separability of an operator space is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAlmostEquality MeasureVectorIntegralUP MeasureVectorIntegralAlmostEquality
  TotalVectorIntegralEstimate SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_vector_integral_almost_dominated_norm]:
    the norm of an actual integral is bounded by an integrable
    almost-everywhere majorant, supporting Federer 4.1.14, p. 371.
    Both functions are modified on the same null set before applying
    the previously proved pointwise estimate. *)
Theorem total_vector_integral_almost_dominated_norm (R:realType)
    (X:choiceType) (Y:lmodType R) (N:Y->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu)
    (f:X->Y) (y:Y) (g:X->R) (b:R):
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  measure_almost_everywhere mu [set x|N (f x)<=g x] ->N y<=b.
Proof.
move=>hIntegral hMajorant hAE.
pose F x:=if N (f x)<=g x then f x else 0.
pose G x:=if N (f x)<=g x then g x else 0.
have hF:measure_almost_equal mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))
    (partial_function_total (fun x=>(F x:real_norm_metric_space hN))).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAE)=>x hx.
  exists (f x);split;first by [].
  change (F x=f x).
  by rewrite /F hx.
have hG:measure_almost_equal mu (real_total_integrand g) (real_total_integrand G).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAE)=>x hx.
  exists (g x)%:E;split;rewrite real_total_integrand_graph;first by [].
  by rewrite /G hx.
have hFI:=measure_vector_integral_almost_equal hm hIntegral hF.
have hGI:=measure_integral_almost_equal hm hMajorant hG.
apply:(@total_vector_integral_dominated_norm R X Y N hN mu hm F y G b hFI hGI)=>x.
rewrite /F /G;case:ifP=>hCase.
- exact:hCase.
- by rewrite (real_seminorm_zero hN.1).
Qed.
