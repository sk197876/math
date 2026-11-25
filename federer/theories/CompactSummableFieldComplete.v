(** Federer (1969), 4.1.18, p. 376: the
    L1 limit used to sum the smooth coefficient
    fields has a representative in the same common
    compact carrier. Reuse the original completeness
    of 2.4.12, p. 87, with a complete target.
    No finite ambient measure or whole-target
    separability is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP PartialZeroExtension
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureAlmostEquality MeasureLpNorm MeasureLpNormAlmostEquality
  MeasureLpConvergence MeasureLpCompleteness MeasureLpFiniteDifference
  MeasureLpAlmostTarget PartialLimitZeroCarrier CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Complete.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Local Notation M:=(real_norm_metric_space hN).
Hypothesis hComplete:is_complete_metric_space M.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation value:=(@compact_summable_field_value R X V N hN mu hm).

(** Source for [compact_summable_field_complete]: a
    common compact carrier survives L1 completion,
    supporting the actual sum xi in Federer
    4.1.18, p. 376. The original norm convergence
    and an actual almost-everywhere convergent subsequence
    are both retained. Empty carriers are allowed. *)
Theorem compact_summable_field_complete
    (K:set X) (hK:compact K) (u:nat->W)
    (hOff:forall i x,~K x->value (u i) x=0)
    (hCauchy:cauchy_in_lp_norm mu N 1
      (fun i=>partial_function_total (value (u i)))):
  exists w:W,(forall x,~K x->value w x=0) /\
    converges_in_lp_norm mu N 1
      (fun i=>partial_function_total (value (u i)))
      (partial_function_total (value w)) /\
    exists s:nat->nat,(forall i,(s i<s i.+1)%N) /\
      measure_almost_everywhere mu (partial_function_limit_locus
        (fun i=>partial_function_total (value (u (s i))))
        (partial_function_total (value w))).
Proof.
pose f:=fun i=>partial_function_total (value (u i)).
have hF:forall i,is_measurable_normed_function mu (f i).
  move=>i;exact:(@compact_summable_field_measurable R X V N hN mu hm (u i)).
have[h [s [hMeas [hStrict [hLimit hConverges]]]]]:=
  @lp_norm_cauchy_complete R X V N hN hComplete mu hm 1 f
    (lexx 1) hF hCauchy.
have hFinite:(measure_lp_norm mu N 1 h< +oo)%E.
  apply:(@lp_norm_limit_finite R X V N hN mu hm 1 f h
    (lexx 1) hF hMeas _ hConverges)=>i.
  exact:(@compact_summable_field_finite R X V N hN mu hm (u i)).
pose hCut:=partial_function_zero_extension (0%R:M) K h.
have hEqual:measure_almost_equal mu h hCut.
  exact:(@partial_almost_limit_zero_carrier R X M 0%R mu hm K
    (fun i=>value (u (s i))) h (fun i x hx=>hOff (s i) x hx) hLimit).
have hCutMeas:=@measurable_normed_almost_equal R X V N hN mu hm h hCut hMeas hEqual.
have hNorm:=@measure_lp_norm_almost_equal R X V N hN mu hm 1 h hCut
  (lexx 1) hMeas.1 hCutMeas.1 hEqual.
have hCutFinite:(measure_lp_norm mu N 1 hCut< +oo)%E by rewrite -hNorm.
have hCutOff:forall x y,partial_function_graph hCut x y->~K x->y=0%R.
  move=>x y hy hx;exact:((partial_function_zero_extension_off _ _ _ hx).1 hy).
have[w [hExtend [hUndefined [hWOff [hAlmost hSize]]]]]:=
  @compact_summable_partial_field_representative R X V N hN mu hm
    hCut hCutMeas hCutFinite K hK hCutOff.
have hTotal:measure_almost_equal mu h (partial_function_total (value w)).
  exact:(measure_almost_equal_trans hm hEqual hAlmost).
have hWMeas:=@compact_summable_field_measurable R X V N hN mu hm w.
exists w;split;first exact:hWOff.
split.
- exact:(@converges_in_lp_norm_almost_target R X V N hN mu hm 1
    (lexx 1) f h (partial_function_total (value w)) hF hMeas hWMeas
    hTotal hConverges).
- exists s;split;first exact:hStrict.
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _
    (measure_almost_everywhere_and hm hLimit hTotal))
    =>x [[v [z [hV [hZ hConvergesZ]]]] [b [hB hWB]]].
  have hSame:z=b:=partial_function_single_valued hZ hB.
  exists v,b;split;first exact:hV.
  split;first exact:hWB.
  by rewrite -hSame.
Qed.
End Complete.
