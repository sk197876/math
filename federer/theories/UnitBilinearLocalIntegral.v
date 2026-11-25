(** Federer (1969), 4.1.7, pp. 355–356:
    local variation summability suffices for the
    current products. This supporting Chapter 2
    estimate combines a unit density with an
    arbitrary locally summable coefficient field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import TensorUP RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  NormBoundedBilinearUP VectorDaniellHypotheses MeasurableBoundedBilinearProduct
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableTotalBasic MeasurableTotalCutoff
  BorelFunctionBasic MeasureStepIntegralIdentification SummableRealFunctionUP SummableRealArithmetic
  MeasureIntegralUP MeasureSubsetIntegral RealSubsetIntegralGraph VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_bilinear_subset_norm_integral]:
    a bounded bilinear product of a unit-bounded
    measurable field and a summable field has
    finite mass integral over the original K,
    supporting Federer 4.1.7, pp. 355–356,
    through 2.4.4, 2.4.6 and 2.4.10.
    No boundedness of the second field is assumed. *)
Theorem unit_bilinear_subset_norm_integral (R:realType) (X:choiceType)
    (A B C:lmodType R) (NA:A->R) (NB:B->R) (NC:C->R)
    (hNA:is_real_norm NA) (hNB:is_real_norm NB) (hNC:is_real_norm NC)
    (mu:set X->\bar R) (hm:is_measure mu)
    (F:A->B->C) (hF:norm_bounded_bilinear NA NB NC F)
    (a:X->A) (b:X->B) (K:set X):
  is_separable_normed_space hNA ->is_separable_normed_space hNB ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(a x:real_norm_metric_space hNA))) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(b x:real_norm_metric_space hNB))) ->
  (forall x,NA (a x)<=1) ->measure_measurable mu K ->
  (exists c:R,is_measure_subset_integral mu K (real_total_integrand (fun x=>NB (b x))) c%:E) ->
  exists c:R,is_measure_subset_integral mu K
    (real_total_integrand (fun x=>NC (F (a x) (b x)))) c%:E.
Proof.
move=>hSepA hSepB hA hB hUnit hK [c hIntegral].
have hProduct:=@measurable_bounded_bilinear_product R X A B C NA NB NC hNA hNB hNC
  mu hm F hF a b hSepA hSepB hA hB.
have hNorm:=@measurable_total_borel_postcomposition R X
  (real_norm_metric_space hNC) (real_line_metric R) mu hm
  (fun x=>(F (a x) (b x):real_norm_metric_space hNC)) (fun z=>NC z) hProduct
  (continuous_borel_function (@real_norm_metric_norm_continuous R C NC hNC)).
pose f x:=if pselect (K x) then NC (F (a x) (b x)) else 0.
pose g x:=if pselect (K x) then NB (b x) else 0.
have hCut:=@measurable_total_cutoff R X (real_line_metric R) mu hm K
  (fun x=>NC (F (a x) (b x))) 0 hK hNorm.
have hFMeas:=@measurable_partial_real_embedding R X mu hm _ hCut.
have hGOn:forall x,K x->g x=NB (b x) by move=>x hx;rewrite /g;case:pselect.
have hGOff:forall x,~K x->g x=0 by move=>x hx;rewrite /g;case:pselect.
have hGIntegral:=(@real_subset_integral_total R X mu K (fun x=>NB (b x)) g c%:E
  hGOn hGOff).1 hIntegral.
have [D [hD hBound]]:=hF.2.
have hScaled:=@real_total_integral_scale R X mu hm g c D hGIntegral.
have hDom:forall x,`|f x|<=D*g x.
  move=>x;rewrite /f /g;case:pselect=>hx.
  - rewrite (ger0_norm (real_seminorm_nonnegative hNC.1 _)).
    apply:le_trans (hBound _ _) _.
    have hFactor:D*NA (a x)<=D.
      have h:=ler_wpM2l hD (hUnit x);by rewrite mulr1 in h.
    rewrite mulrA.
    exact:(ler_wpM2r (real_seminorm_nonnegative hNB.1 (b x)) hFactor).
  - by rewrite normr0 mulr0.
have [d [hValue _]]:=@real_total_dominated_integral R X mu hm f (fun x=>D*g x)
  (D*c) hFMeas hScaled hDom.
exists d;apply:(@real_subset_integral_total R X mu K
  (fun x=>NC (F (a x) (b x))) f d%:E _ _).2 hValue.
- by move=>x hx;rewrite /f;case:pselect.
- by move=>x hx;rewrite /f;case:pselect.
Qed.
