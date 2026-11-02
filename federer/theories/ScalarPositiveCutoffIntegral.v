(** Federer (1969), 3.2.36, p. 273: reduce the positive-radius
    polar integral to the open radius interval, retaining the endpoint
    as a genuine scalar null-set exception. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension SummableRealFunctionUP LebesgueScalarMeasure MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_positive_cutoff_integral]: endpoint removal in
    the radius integral of Federer 3.2.36, p. 273, using the scalar
    singleton nullity of 2.5.17, p. 111, and null modification of
    integrals in 2.4.3(2), p. 81. The original partial integrand has
    the specified values only on 0<s<r and is zero for s>r;
    no value is assumed at r, including the nonzero zero-degree case. *)
Lemma scalar_positive_cutoff_integral (R:realType) (F:partial_function R (extended_real_line R))
    (g:R->R) (r:R) a:
  (forall s,0<s ->s<r ->partial_function_graph F s (g s)%:E) ->
  (forall s,r<s ->partial_function_graph F s (0:extended_real_line R)) ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set s:R|0<s] F a ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (real_total_integrand g) a.
Proof.
move=>hOn hOff hI.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
have hAway:measure_almost_everywhere mu [set s:R|s!=r].
  have hSet:(~` [set s:R|s!=r])=[set r].
    apply/seteqP; split=>s.
    - move=>hs; case:(eqVneq s r)=>[he|hne]; first by rewrite he.
      exfalso; exact:hs hne.
    - move=>hs hn; have he:s=r by exact hs.
      move:hn; change (s!=r ->False); by rewrite he eqxx.
  rewrite /measure_almost_everywhere hSet; exact:lebesgue_scalar_singleton.
apply:(measure_integral_almost_equal hm hI).
apply:(measure_almost_everywhere_mono hm _ hAway)=>s hne.
case:(ltP 0 s)=>hs.
- case:(ltP s r)=>hsr.
  + exists (g s)%:E; split.
    * apply/partial_function_zero_extension_graph; left; split=>//; exact:hOn s hs hsr.
    * apply/partial_function_zero_extension_graph; left; split; last exact/real_total_integrand_graph.
      by split.
  + have hrs:r<s by rewrite lt_neqAle eq_sym hne hsr.
    exists (0:extended_real_line R); split.
    * apply/partial_function_zero_extension_graph; left; split=>//; exact:hOff s hrs.
    * apply/partial_function_zero_extension_graph; right; split=>//.
      by move=>[_ hBad]; move:hBad; rewrite ltNge hsr.
- have hnPos:~[set t:R|0<t] s.
    move=>hBad; have hh:0<s:=hBad.
    by move:hh; rewrite ltNge hs.
  have hnInt:~real_open_interval 0 r s.
    by move=>[hBad _]; move:hBad; rewrite ltNge hs.
  exists (0:extended_real_line R); split.
  + apply/(partial_function_zero_extension_off _ _ _ hnPos); by [].
  + apply/(partial_function_zero_extension_off _ _ _ hnInt); by [].
Qed.
