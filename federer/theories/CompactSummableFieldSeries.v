(** Federer (1969), 4.1.18, p. 376: the
    smooth coefficient fields with a common compact carrier
    have an actual L1 sum and the original numerical
    tail bounds. Reuse the L1 completeness of 2.4.12,
    p. 87, its lower-limit inequality, and the
    exact numerical tails of 2.1.1(13), p. 53. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP
  PartialFunctionUP PartialFunctionBasic PartialDifferenceLimit PartialNormedArithmetic
  PartialFunctionLimitUP CauchyIndexSelectionLaws MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableNormedDifference MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureLpNorm MeasureLpConvergence MeasureLpNormLowerLimit
  ExtendedLowerLimit ExtendedLowerLimitUpperBound
  NonnegativeSum NonnegativeSequenceTail NonnegativeRealSeriesTails
  RealSeminormSummablePrefixes CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldFinitePrefix
  CompactSummableFieldComplete.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Series.
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
Local Notation hSize:=(@compact_summable_field_size_seminorm R X V N hN mu hm).
Variable u:nat->W.
Variable a:nat->R.
Hypothesis ha:forall i,0<=a i.
Hypothesis hFinite:(nonnegative_sum setT (fun i=>(a i)%:E)< +oo)%E.
Hypothesis hBound:forall i,size (u i)<=a i.
Local Notation S:=(fun k=>\sum_(i<k) u i).
Local Notation t:=(nonnegative_real_series_tail a).

(** Source for [compact_summable_field_prefix_cauchy]:
    the original L1 Cauchy estimate for the finite
    coefficient sums in Federer 4.1.18, p. 376. *)
Lemma compact_summable_field_prefix_cauchy:
  cauchy_in_lp_norm mu N 1
    (fun k=>partial_function_total (value (S k))).
Proof.
move=>epsilon hEpsilon.
have[L hL]:=@real_seminorm_prefix_cauchy R W size hSize u a ha hFinite hBound
  epsilon hEpsilon.
exists L=>i j hI hJ.
rewrite (@compact_summable_field_distance R X V N hN mu hm) lte_fin.
exact:(hL i j hI hJ).
Qed.

(** Source for [compact_summable_field_series_exists]:
    xi=sum xi_i has a compact representative,
    retains the exact original L1 convergence and
    numerical tails, and has an actual almost-everywhere
    convergent subsequence. These are the L1 summation
    steps of Federer 4.1.18, p. 376. *)
Theorem compact_summable_field_series_exists (K:set X) (hK:compact K)
    (hOff:forall i x,~K x->value (u i) x=0):
  exists w:W,(forall x,~K x->value w x=0) /\
    converges_in_lp_norm mu N 1
      (fun k=>partial_function_total (value (S k)))
      (partial_function_total (value w)) /\
    (forall k,size (w-S k)<=t k) /\
    exists s:nat->nat,(forall i,(s i<s i.+1)%N) /\
      measure_almost_everywhere mu (partial_function_limit_locus
        (fun i=>partial_function_total (value (S (s i))))
        (partial_function_total (value w))).
Proof.
have hSOff:=@compact_summable_field_prefix_carrier R X V N hN mu hm K u hOff.
have[w [hWOff [hConverges [s [hStrict hLimit]]]]]:=
  @compact_summable_field_complete R X V N hN hComplete mu hm K hK S
    hSOff compact_summable_field_prefix_cauchy.
exists w;split;first exact:hWOff.
split;first exact:hConverges.
split;last by exists s;split.
move=>k.
have hIndex:=@strict_index_sequence_dominates s hStrict.
pose f:=fun i=>partial_function_total (value (S (s i))).
pose z:=partial_function_total (value (S k)).
pose g:=partial_function_total (value w).
have hF:forall i,is_measurable_normed_function mu (f i).
  move=>i;exact:(@compact_summable_field_measurable R X V N hN mu hm (S (s i))).
have hZ:=@compact_summable_field_measurable R X V N hN mu hm (S k).
have hG:=@compact_summable_field_measurable R X V N hN mu hm w.
have hDifferenceLimit:=@partial_difference_almost_limit R X V N hN mu hm
  z f g (measurable_function_domain hZ.1) hLimit.
have hLower:=@measure_lp_norm_lower_semicontinuous R X V N hN mu hm 1
  (fun i=>partial_vector_subtract z (f i)) (partial_vector_subtract z g)
  (lexx 1)
  (fun i=>(@measurable_normed_function_subtract R X V N hN mu hm z (f i) hZ (hF i)).1)
  (@measurable_normed_function_subtract R X V N hN mu hm z g hZ hG).1
  hDifferenceLimit.
have hUpper:(extended_lower_limit
    (fun i=>measure_lp_norm mu N 1 (partial_vector_subtract z (f i)))<=(t k)%:E)%E.
  apply:(extended_lower_limit_eventual_upper_bound (extended_lower_limit_laws _) _).
  exists k=>i hI.
  change (measure_lp_distance mu N 1 z (f i)<=(t k)%:E)%E.
  rewrite (@compact_summable_field_distance R X V N hN mu hm) lee_fin
    (real_seminorm_subtract hSize).
  have hKI:(k<=s i)%N:=leq_trans hI (hIndex i).
  have hTail:=@real_seminorm_prefix_tail_bound R W size hSize u a ha hFinite hBound k ((s i-k)%N).
  rewrite subnKC // in hTail.
  apply:(le_trans hTail _).
  rewrite lerBlDr lerDl;exact:(@nonnegative_real_series_tail_nonnegative R a hFinite (s i)).
have hResult:=le_trans hLower hUpper.
change (is_true ((measure_lp_distance mu N 1 z g<=(t k)%:E)%E)) in hResult.
rewrite (@compact_summable_field_distance R X V N hN mu hm) lee_fin
  (real_seminorm_subtract hSize) in hResult.
exact:hResult.
Qed.
End Series.
