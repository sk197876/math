(** Federer (1969), 4.1.7, pp. 355–356:
    the measurable-field extension includes every
    original smooth field. This supporting fact
    uses compact boundedness and Radon compact
    finiteness, already used in 2.5.13,
    pp. 106–107. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionPreimages RealNormUP NormMetric RealMetricBackground NormMetricContinuity CompactMaximum
  CurrentMeasurableMultiplierUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostBasic
  RadonMeasureUP RadonBorelRegularity MeasurableFunctionUP MeasurableTotalCutoff
  MeasureStepIntegralIdentification MeasureIntegralUP MeasureSubsetIntegral RealSubsetIntegralGraph
  SummableRealFunctionUP SummableRealArithmetic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureCharacteristicIntegral VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_radon_field_locally_summable]:
    every continuous field is measurable and
    locally norm-summable for a Radon measure,
    supporting Federer 4.1.7, pp. 355–356.
    The source need not be boundedly compact,
    and the field need not have compact support. *)
Theorem continuous_radon_field_locally_summable (R:realType) (X:topologicalType)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu) (f:X->V):
  continuous (fun x=>(f x:real_norm_metric_space hNV)) ->
  is_locally_summable_current_field hNV mu f.
Proof.
move=>hF.
have hMeas:is_measure_measurable_function mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNV))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hm.
  - move=>G hG;rewrite partial_function_total_preimage.
    exact:(@radon_open_measurable R X mu hr (f @^-1` G)
      ((@continuousP X (real_norm_metric_space hNV) f).1 hF G hG)).
have hNorm:continuous (fun x:X=>(NV (f x):real_line_metric R)).
  move=>x;exact:(continuous_comp (hF x) (@real_norm_metric_norm_continuous R V NV hNV (f x))).
have hNormMeas:is_measure_measurable_function mu
    (partial_function_total (fun x:X=>(NV (f x):real_line_metric R))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hm.
  - move=>G hG;rewrite partial_function_total_preimage.
    exact:(@radon_open_measurable R X mu hr ((fun x=>NV (f x)) @^-1` G)
      ((@continuousP X (real_line_metric R) (fun x=>NV (f x))).1 hNorm G hG)).
split;first exact:hMeas.
move=>K hK.
have hBound:exists M:R,0<=M /\forall x,K x->NV (f x)<=M.
  case:(pselect (K !=set0))=>hNonempty.
  - have [a [ha hMax]]:=@continuous_compact_maximum R X K (fun x=>NV (f x)) hNonempty hK hNorm.
    exists (NV (f a));split;first exact:real_seminorm_nonnegative hNV.1 _.
    exact:hMax.
  - exists 0;split;first exact:lexx.
    move=>x hx;exact:False_ind _ (hNonempty (ex_intro _ x hx)).
have [M [hM hBoundK]]:=hBound.
pose s:=@CharacteristicFunction.value R X K.
have hs:=@CharacteristicFunction.laws R X K.
have hKm:=@radon_compact_measurable R X mu hm hr K hK.
have hFinite:mu K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K));exact:(@radon_compact_finite R X mu hr K hK).
have hChar:=@measure_characteristic_integral R X mu hm K s hs hKm.
rewrite -(fineK hFinite) in hChar.
have hScale:=@real_total_integral_scale R X mu hm s (fine (mu K)) M hChar.
pose g x:=if pselect (K x) then NV (f x) else 0.
have hCut:=@measurable_total_cutoff R X (real_line_metric R) mu hm K
  (fun x=>NV (f x)) 0 hKm hNormMeas.
have hG:=@measurable_partial_real_embedding R X mu hm _ hCut.
have hDom:forall x,`|g x|<=M*s x.
  move=>x;rewrite /g /s;case:pselect=>hx.
  - rewrite (characteristic_on_set hs hx) mulr1
      (ger0_norm (real_seminorm_nonnegative hNV.1 _));exact:hBoundK x hx.
  - by rewrite (characteristic_off_set hs hx) mulr0 normr0.
have [c [hValue _]]:=@real_total_dominated_integral R X mu hm g (fun x=>M*s x)
  (M*fine (mu K)) hG hScale hDom.
exists c;apply:(@real_subset_integral_total R X mu K (fun x=>NV (f x)) g c%:E _ _).2 hValue.
- by move=>x hx;rewrite /g;case:pselect.
- by move=>x hx;rewrite /g;case:pselect.
Qed.
