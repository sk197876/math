(** Federer (1969), 4.1.2, p. 347: dominated passage
    to the input derivative under the original vector integral.
    The original scalar bounded-convergence theorem controls the
    actual norm error, and the vector-integral norm bound completes
    the passage to Banach values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasurableFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP SummableRealFunctionUP
  PartialExtendedOrderLoci PartialAbsolutePartsGraph PartialDominatedConvergence
  MeasureVectorIntegralUP MeasureBoundedConvergence MeasureIntegralUniqueness MeasureConullZeroIntegral
  ExtendedRealOrderLimit RealErrorOrderLimit TotalVectorIntegralArithmetic
  TotalVectorNormIntegrability TotalVectorIntegralEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_vector_integral_dominated_limit]: the dominated
    integral passage supporting D_j(Phi*f)=Phi*D_j f for locally
    Lipschitz reflexive-valued inputs, Federer 4.1.2, p. 347.
    The supplied vectors are actual integrals. No whole-target
    separability or completeness premise is added to this limit lemma. *)
Theorem total_vector_integral_dominated_limit (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (f:nat->X->Y) (g:X->Y)
    (a:nat->Y) (b:Y) (H:X->R):
  (forall m,is_measure_vector_integral mu
    (partial_function_total (fun x=>(f m x:real_norm_metric_space hNY))) (a m)) ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(g x:real_norm_metric_space hNY))) b ->
  is_measure_summable mu (real_total_integrand H) ->
  (forall m x,NY (f m x-g x)<=H x) ->
  measure_almost_everywhere mu [set x|forall eta:R,0<eta ->
    exists N:nat,forall m,(N<=m)%N ->NY (f m x-g x)<eta] ->
  forall eta:R,0<eta ->exists N:nat,forall m,(N<=m)%N ->NY (a m-b)<eta.
Proof.
move=>hF hG hH hDom hPoint eta hEta.
pose err m x:=f m x-g x.
have hI m:is_measure_vector_integral mu
    (partial_function_total (fun x=>(err m x:real_norm_metric_space hNY))) (a m-b).
  exact:(@total_vector_integral_subtract R X Y NY hNY mu hm
    (f m) g (a m) b (hF m) hG).
pose u m:=real_total_integrand (fun x=>NY (err m x)).
pose z:=real_total_integrand (fun _ : X=>(0:R)).
have hMeas m:is_measure_measurable_function mu (u m).
  exact:(@total_vector_norm_integrand_measurable R X Y NY hNY mu hm (err m) (hI m).1.2.1.1).
have hZero:is_measure_integral mu z 0%E.
  apply:(@measure_almost_zero_integral R X mu hm z).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=>x _; exact/real_total_integrand_graph.
have hBounds m:measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (u m))
      (real_total_integrand H)).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=>x _.
  exists (NY (err m x))%:E,(H x)%:E; split.
  - exists (NY (err m x))%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin (ger0_norm (real_seminorm_nonnegative hNY.1 (err m x))).
  - split; first exact/real_total_integrand_graph.
    rewrite lee_fin; exact:hDom m x.
have hLimit:measure_almost_everywhere mu
    (partial_extended_convergence_locus u z).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hPoint).
  move=>x hx; exists (fun m=>(NY (err m x))%:E),(0:R)%:E; split.
  - move=>m; exact/real_total_integrand_graph.
  - split; first exact/real_total_integrand_graph.
    apply:real_error_extended_order_limit=>r hr.
    have[N hN]:=hx r hr; exists N=>m hmN.
    rewrite subr0 (ger0_norm (real_seminorm_nonnegative hNY.1 (err m x))).
    exact:hN m hmN.
have[c [d [s [hCI [hZI [_ [_ hCL]]]]]]]:=@measure_bounded_convergence R X mu hm u z
  (real_total_integrand H) hH hMeas hZero.1 hBounds hLimit.
have hS:s%:E=0%E:=measure_integral_unique hZI hZero.
rewrite hS in hCL.
have hEtaE:(0<eta%:E)%E by rewrite lte_fin.
have[N hN]:=hCL.2 eta%:E hEtaE.
exists N=>m hmN.
have hSmall:c m<eta by have:=hN m hmN; rewrite lte_fin.
have hBound:NY (a m-b)<=c m.
  exact:(@total_vector_integral_dominated_norm R X Y NY hNY mu hm (err m) (a m-b)
    (fun x=>NY (err m x)) (c m) (hI m) (hCI m) (fun _=>lexx _)).
exact:le_lt_trans hBound hSmall.
Qed.
