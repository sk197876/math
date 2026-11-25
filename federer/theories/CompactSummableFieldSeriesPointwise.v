(** Federer (1969), 4.1.18, p. 376: the
    field xi is the literal almost-everywhere sum of
    the smooth coefficient series, with its original
    common compact carrier, L1 convergence and exact
    numerical error tails. No finite ambient measure
    or quotient-valued substitute is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP
  PartialFunctionBasic PartialFunctionLimitUP MeasureUP MeasureAlmostUP
  MeasureLpConvergence NonnegativeSum NonnegativeRealSeriesTails
  CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldSeries CompactSummableFieldAbsoluteSeries
  PartialFullLimitFromSubsequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PointwiseSeries.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Hypothesis hComplete:is_complete_metric_space (real_norm_metric_space hN).
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation value:=(@compact_summable_field_value R X V N hN mu hm).
Local Notation size:=(@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_pointwise_series]:
    the complete original compact-field summation step
    of Federer 4.1.18, p. 376: the
    whole pointwise series, original L1 limit and
    exact tail estimate refer to the same actual
    compact representative. Empty carriers are allowed. *)
Theorem compact_summable_field_pointwise_series (u:nat->W) (a:nat->R)
    (K:set X) (hK:compact K):
  (forall i,0<=a i)->
  (nonnegative_sum setT (fun i=>(a i)%:E)< +oo)%E->
  (forall i,size (u i)<=a i)->
  (forall i x,~K x->value (u i) x=0)->
  exists w:W,(forall x,~K x->value w x=0) /\
    converges_in_lp_norm mu N 1
      (fun k=>partial_function_total (value (\sum_(i<k) u i)))
      (partial_function_total (value w)) /\
    (forall k,size (w-\sum_(i<k) u i)<=nonnegative_real_series_tail a k) /\
    measure_almost_everywhere mu (partial_function_limit_locus
      (fun k=>partial_function_total (value (\sum_(i<k) u i)))
      (partial_function_total (value w))).
Proof.
move=>ha hFinite hBound hOff.
have[w [hWOff [hLone [hTail [s [hStrict hLimit]]]]]]:=
  @compact_summable_field_series_exists R X V N hN hComplete mu hm
    u a ha hFinite hBound K hK hOff.
have hPointwise:=@compact_summable_field_absolute_series R X V N hN hComplete mu hm
  u a hBound hFinite.
exists w;split;first exact:hWOff.
split;first exact:hLone.
split;first exact:hTail.
exact:(@partial_full_limit_from_subsequence R X (real_norm_metric_space hN)
  mu hm (fun k=>value (\sum_(i<k) u i))
  (partial_function_total (value w)) s hStrict hPointwise hLimit).
Qed.
End PointwiseSeries.
