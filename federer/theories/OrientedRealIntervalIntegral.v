(**  Federer (1969), 3.2.6, pp. 245–246:
    the scalar substitution formula allows either order of
    endpoint values. This supporting oriented convention
    extends the ordered half-open notation of 2.4.10,
    p. 85, by negation under reversal. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology EndpointLevelSigns
  ScalarSignedMultiplicityAlmost SummableRealFunctionUP PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialExtendedArithmetic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntervalIntegral MeasureSubsetIntegral
  MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence MeasureIntegralNegation MeasureIntegralNegationLaw LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(**  Source for [is_measure_oriented_real_interval_integral]:
    supporting notation for the final display of Federer
    3.2.6, p. 245. Ordered endpoints use exactly
    2.4.10, p. 85; reversed endpoints negate the
    ordered value. Equality is included in the ordered branch. *)
Definition is_measure_oriented_real_interval_integral (R:realType) (mu : set R -> \bar R)
    (a b:R) (f:partial_function R (extended_real_line R)) (z : \bar R) :=
  if a<=b then is_measure_real_interval_integral mu a%:E b%:E f z
  else is_measure_real_interval_integral mu b%:E a%:E f (-z)%E.

(**  Source for [oriented_level_indicator_ordered]: supporting
    ordered endpoint calculation in Federer 3.2.6,
    p. 246. The opposite open interval is empty. *)
Lemma oriented_level_indicator_ordered (R:realType) (a b y:R):
  a<=b -> oriented_level_indicator a b y=(((a<y)&&(y<b))%R)%:R.
Proof.
move=>hab; have hn:((b<y)&&(y<a))=false.
  apply/negbTE/negP=>/andP[hby hya].
  have hh:=lt_le_trans hya hab; by have:=lt_trans hby hh; rewrite ltxx.
by rewrite /oriented_level_indicator hn /= subr0.
Qed.

(**  Source for [oriented_level_indicator_reversed]: supporting
    reversed endpoint calculation for the second identity
    of Federer 3.2.6, p. 245. *)
Lemma oriented_level_indicator_reversed (R:realType) (a b y:R):
  b<=a -> oriented_level_indicator a b y= -(((b<y)&&(y<a))%R)%:R.
Proof.
move=>hba; have hn:((a<y)&&(y<b))=false.
  apply/negbTE/negP=>/andP[hay hyb].
  have hh:=lt_le_trans hyb hba; by have:=lt_trans hay hh; rewrite ltxx.
by rewrite /oriented_level_indicator hn /= sub0r.
Qed.

(**  Source for [oriented_indicator_ordered_cutoff_almost]:
    the omission or inclusion of the upper endpoint in
    Federer 3.2.6, p. 246. The upper endpoint
    is Lebesgue null; arbitrary g is retained. *)
Lemma oriented_indicator_ordered_cutoff_almost (R:realType) (g:R->R) (a b:R):
  a<=b -> measure_almost_equal (@lebesgue_scalar_measure R)
    (scalar_oriented_interval_integrand g a b)
    (partial_function_zero_extension (0:extended_real_line R)
      (measure_half_open_interval (fun x:R=>x%:E) a%:E b%:E) (real_total_integrand g)).
Proof.
move=>hab; have hm:=lebesgue_scalar_is_measure R.
have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R) (~` [set b]).
  by rewrite /measure_almost_everywhere setCK lebesgue_scalar_singleton.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ hOff)=>y hy.
have hyb:y!=b by apply/eqP=>he; exact (hy he).
have hInd:oriented_level_indicator a b y=(((a<y)&&(y<=b))%R)%:R.
  by rewrite (oriented_level_indicator_ordered y hab) (lt_neqAle y b) hyb /=.
exists (g y * oriented_level_indicator a b y)%:E; split; first exact:erefl.
case:(boolP ((a<y)&&(y<=b)))=>hRange.
- have hMem:(measure_half_open_interval (fun x:R=>x%:E) a%:E b%:E) y.
    by rewrite /measure_half_open_interval /= !lte_fin !lee_fin.
  apply/partial_function_zero_extension_graph; left; split=>//.
  apply/real_total_integrand_graph; by rewrite hInd hRange /= mulr1.
- have hNot:~(measure_half_open_interval (fun x:R=>x%:E) a%:E b%:E) y.
    by rewrite /measure_half_open_interval /= !lte_fin !lee_fin; apply/negP.
  apply/partial_function_zero_extension_graph; right; split=>//.
  by rewrite hInd (negbTE hRange) /= mulr0.
Qed.

(**  Source for [oriented_interval_integral_from_indicator]:
    interval notation in the second equation of Federer
    3.2.6, p. 245, for every endpoint order.
    No independent measurability of g is assumed. *)
Theorem oriented_interval_integral_from_indicator (R:realType) (g:R->R) (a b:R) z:
  is_measure_integral (@lebesgue_scalar_measure R) (scalar_oriented_interval_integrand g a b) z ->
  is_measure_oriented_real_interval_integral (@lebesgue_scalar_measure R) a b (real_total_integrand g) z.
Proof.
move=>hi; have hm:=lebesgue_scalar_is_measure R.
rewrite /is_measure_oriented_real_interval_integral.
case:(leP a b)=>hab.
- exact (measure_integral_almost_equal hm hi (oriented_indicator_ordered_cutoff_almost g hab)).
- have hn:=measure_integral_negation hm hi.
  have he:forall y w,partial_function_graph
      (partial_extended_function_negate (scalar_oriented_interval_integrand g a b)) y w <->
      partial_function_graph (scalar_oriented_interval_integrand g b a) y w.
    move=>y w.
    have hVal:-(g y * oriented_level_indicator a b y)=g y * oriented_level_indicator b a y.
      rewrite (oriented_level_indicator_reversed y (ltW hab))
        (oriented_level_indicator_ordered y (ltW hab)) mulrN opprK; exact:erefl.
    split.
    + move=>[v [hv hw]].
      change ((g y * oriented_level_indicator a b y)%:E=v) in hv.
      change ((g y * oriented_level_indicator b a y)%:E=w).
      by rewrite -hw -hv -EFinN hVal.
    + move=>hw; exists (g y * oriented_level_indicator a b y)%:E; split; first exact:erefl.
      by rewrite -EFinN hVal.
  have hn':=measure_integral_graph_equivalent he hn.
  exact (measure_integral_almost_equal hm hn' (oriented_indicator_ordered_cutoff_almost g (ltW hab))).
Qed.
