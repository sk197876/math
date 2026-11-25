(** Federer (1969), 4.1.18, p. 376: the
    coefficient series converges almost everywhere. Integrate
    the nonnegative sum of the original pointwise norms
    by 2.4.8, p. 84, then apply the
    complete-metric series argument of 2.3.9, p. 79.
    Neither a finite ambient measure nor a separable
    whole target is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence SummableRealFunctionUP
  MeasureUpperIntegralPositivePart
  PartialExtendedOrderLoci TotalNonnegativeSeriesIntegral
  NonnegativeSum SummableMetricIncrementLimit CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AbsoluteSeries.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Hypothesis hComplete:is_complete_metric_space (real_norm_metric_space hN).
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation M:=(real_norm_metric_space hN).
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation value:=(@compact_summable_field_value R X V N hN mu hm).
Local Notation size:=(@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_absolute_series]:
    actual almost-everywhere convergence of the whole
    coefficient series in Federer 4.1.18, p. 376,
    from the printed sum of its L1 norms. *)
Theorem compact_summable_field_absolute_series (u:nat->W) (a:nat->R):
  (forall i,size (u i)<=a i)->
  (nonnegative_sum setT (fun i=>(a i)%:E)< +oo)%E->
  measure_almost_everywhere mu [set x | exists z:M,
    (fun k=>value (\sum_(i<k) u i) x) @ \oo --> z].
Proof.
move=>hBound hFinite.
pose b:=fun i=>(size (u i))%:E.
have hBFinite:(nonnegative_sum setT b< +oo)%E.
  apply:(le_lt_trans _ hFinite).
  apply:nonnegative_sum_mono=>i _;rewrite lee_fin;exact:hBound i.
pose f:=fun i x=>(N (value (u i) x))%:E.
have hF:forall i x,(0<=f i x)%E.
  move=>i x;rewrite lee_fin;exact:(real_seminorm_nonnegative hN.1 _).
have hEach:forall i,is_measure_integral mu (partial_function_total (f i)) (b i).
  move=>i;apply:(@measure_integral_graph_equivalent R X mu _ _ (b i) _
    (@compact_summable_field_size_integral R X V N hN mu hm (u i)))
    =>x y;exact:real_total_integrand_graph.
have hIntegral:=@total_nonnegative_series_integral R X mu hm f b hF hEach.
have hUpper:=@measure_upper_integral_unique R X mu
  (partial_function_total (fun x=>nonnegative_sum setT (fun i=>f i x)))
  _ _ (measure_upper_integral_specification mu _) hIntegral.2.1.
have hUpperFinite:(measure_upper_integral mu
    (partial_function_total (fun x=>nonnegative_sum setT (fun i=>f i x)))< +oo)%E.
  by rewrite hUpper.
have hAlmost:=(@measure_finite_upper_integral_consequences R X mu hm _ hUpperFinite).2.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)
  =>x [y [hY hYFinite]].
have hPointFinite:(nonnegative_sum setT (fun i=>f i x)< +oo)%E.
  have hValue:nonnegative_sum setT (fun i=>f i x)=y:=hY.
  by rewrite hValue.
have hStep:forall k,(0<=k)%N->
    ((mdist (value (\sum_(i<k.+1) u i) x)
      (value (\sum_(i<k) u i) x))%:E<=f k x)%E.
  move=>k _;rewrite real_norm_metric_distanceE big_ord_recr /=
    compact_summable_field_value_add /= addrAC subrr add0r.
  exact:lexx.
have[z [hLimit hTail]]:=@summable_metric_increment_limit R M hComplete
  (fun k=>value (\sum_(i<k) u i) x) (fun i=>f i x) 0
  (fun i=>hF i x) hPointFinite hStep.
by exists z.
Qed.
End AbsoluteSeries.
