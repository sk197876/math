(** Federer (1969), 4.1.7, p. 359:
    a measurable field bounded on each
    compact set is locally norm-summable for
    the original Radon measure. This supporting
    adapter applies the domination and characteristic
    integral laws of 2.4.4–2.4.6, pp. 82–84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity RealMetricBackground
  PartialFunctionBasic MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity MeasurableFunctionUP
  MeasurableTotalBasic MeasurableTotalCutoff BorelFunctionBasic MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureSubsetIntegral RealSubsetIntegralGraph SummableRealFunctionUP
  SummableRealArithmetic CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_compact_norm_integral]:
    a compact norm bound gives the
    finite original subset integral, supporting
    Federer 4.1.7, p. 359. The measure
    and the field need not be finite
    or bounded on the whole domain. *)
Theorem measurable_compact_norm_integral (R:realType) (X:topologicalType)
    (Y:lmodType R) (N:Y->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (f:X->Y) (K:set X) (C:R):
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))->
  compact K->0<=C->(forall x,K x->N (f x)<=C)->
  exists c:R,is_measure_subset_integral mu K (real_total_integrand (fun x=>N (f x))) c%:E.
Proof.
move=>hF hK hC hBound.
have hNorm:=@measurable_total_borel_postcomposition R X (real_norm_metric_space hN)
  (real_line_metric R) mu hm (fun x=>(f x:real_norm_metric_space hN)) (fun y=>N y) hF
  (continuous_borel_function (@real_norm_metric_norm_continuous R Y N hN)).
have hMeasK:=@radon_compact_measurable R X mu hm hr K hK.
have hFinite:mu K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K));exact:(@radon_compact_finite R X mu hr K hK).
pose s:=@CharacteristicFunction.value R X K.
have hs:=@CharacteristicFunction.laws R X K.
have hChar:=@measure_characteristic_integral R X mu hm K s hs hMeasK.
rewrite -(fineK hFinite) in hChar.
have hScale:=@real_total_integral_scale R X mu hm s (fine (mu K)) C hChar.
pose g x:=if pselect (K x) then N (f x) else 0.
have hCut:=@measurable_total_cutoff R X (real_line_metric R) mu hm K
  (fun x=>N (f x)) 0 hMeasK hNorm.
have hG:=@measurable_partial_real_embedding R X mu hm _ hCut.
have hDom x:`|g x|<=C*s x.
  rewrite /g /s;case:pselect=>hx.
  - rewrite (characteristic_on_set hs hx) mulr1
      (ger0_norm (real_seminorm_nonnegative hN.1 (f x)));exact:hBound x hx.
  - by rewrite (characteristic_off_set hs hx) mulr0 normr0.
have [c [hValue _]]:=@real_total_dominated_integral R X mu hm g (fun x=>C*s x)
  (C*fine (mu K)) hG hScale hDom.
exists c;apply:(@real_subset_integral_total R X mu K (fun x=>N (f x)) g c%:E _ _).2 hValue.
- by move=>x hx;rewrite /g;case:pselect.
- by move=>x hx;rewrite /g;case:pselect.
Qed.
