(** Federer (1969), 3.2.7, p. 246, final
    counterexample: the weight u(x)=x on the whole
    real line is not integrable. Prove the actual
    integral-domain failure, without a principal-value convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialFunctionPostcomposition PartialAbsolutePartsGraph PartialExtendedOrderLoci
  SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAbsolute MeasureIntegralComparison
  MeasureExtendedCharacteristicIntegral MeasureIntegralGraphEquivalence MeasureIntegralNegation MeasureIntegralNegationLaw
  MeasureIntegralUniqueness MeasurePushforward InjectivePushforwardIntegral ScalarReflectionMeasure ExtendedNaturalMultiples
  LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_identity_not_summable]: supporting
    global-weight obstruction in the last example of
    Federer 3.2.7, p. 246. The integral of
    |x| dominates the length n of [1,n+1]
    for every n, and hence cannot be finite. *)
Lemma scalar_identity_not_summable (R:realType):
  ~is_measure_summable (@lebesgue_scalar_measure R) (real_total_integrand (fun x:R=>x)).
Proof.
move=>hSum; have hm:=lebesgue_scalar_is_measure R.
have [J hJ]:=measure_summable_absolute_value hm hSum.
have hBound n:((n%:R:R)%:E<=J%:E)%E.
  pose B:=(`[1%R,(n%:R+1)%R]:set (real_line_metric R)).
  pose chi:=@CharacteristicFunction.value R [the choiceType of real_line_metric R] B.
  have hChi:is_characteristic_function B chi:=@CharacteristicFunction.laws R [the choiceType of real_line_metric R] B.
  have hB:measure_measurable (@lebesgue_scalar_measure R) B.
    exact (borel_regular_borel_measurable hm (lebesgue_scalar_borel_regular R)
      (closed_borel_set (@segment_closed_real R 1 (n%:R+1)))).
  have hOrder:(1:R)<=n%:R+1 by have hn:=ler0n R n; lra.
  have hMass:lebesgue_scalar_measure B=(n%:R:R)%:E.
    rewrite /B (lebesgue_scalar_segment hOrder); congr (_%:E); lra.
  have hi:=measure_total_characteristic_integral hm hChi hB.
  rewrite hMass in hi.
  apply:(measure_integral_monotone hm hi hJ).
  apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_true hm))=>x _.
  exists (chi x)%:E,`|x|%:E; split; first exact:erefl; split.
  - exists x%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - rewrite lee_fin; case:(pselect (B x))=>hx.
    + rewrite (characteristic_on_set hChi hx).
      have hx':=hx; move:hx'; rewrite /B /= in_itv /= =>/andP[hxl hxu].
      exact (le_trans hxl (ler_norm x)).
    + rewrite (characteristic_off_set hChi hx); exact:normr_ge0.
have hInf:J%:E=(+oo : \bar R)%E.
  apply:(@positive_natural_multiples_force_infinity R 1 J%:E (ltac:(by rewrite lte_fin ltr01)))=>n.
  by rewrite mule1; exact:hBound.
have hf:(J%:E< +oo)%E:=ltry J.
by rewrite hInf ltxx in hf.
Qed.

(** Source for [scalar_identity_not_integrable]: the
    last weight in Federer 3.2.7, p. 246,
    has no actual signed Lebesgue integral. Reflection
    would negate its integral while preserving it; an
    infinite value is impossible and a finite value
    contradicts the preceding absolute-integral obstruction. *)
Theorem scalar_identity_not_integrable (R:realType):
  ~is_measure_integrable (@lebesgue_scalar_measure R) (real_total_integrand (fun x:R=>x)).
Proof.
move=>[a ha]; have hm:=lebesgue_scalar_is_measure R.
pose F:=real_total_integrand (fun x:R=>x).
have hPush:measure_pushforward (fun x:real_line_metric R=> -x) (@lebesgue_scalar_measure R)=
    @lebesgue_scalar_measure R.
  apply:funext=>B; exact:scalar_reflection_preserves_length.
have hInj:injective (fun x:real_line_metric R=> -x) by exact:oppr_inj.
have hTransport:=@injective_pushforward_integral_iff R [the choiceType of real_line_metric R]
  [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R) hm
  (fun x:real_line_metric R=> -x) F hInj a.
rewrite hPush in hTransport.
have hNegSame:=(hTransport.2 ha).
have hNegOpp:=measure_integral_negation hm ha.
have he:forall x z,partial_function_graph (partial_extended_function_negate F) x z <->
    partial_function_graph (partial_function_precompose (fun t:R=> -t) F) x z.
  move=>x z; split.
  - move=>[v [hv hw]].
    have hv':=(real_total_integrand_graph (fun t:R=>t) x v).1 hv.
    apply/real_total_integrand_graph; by rewrite -hw -hv' -EFinN.
  - move/real_total_integrand_graph=>hz.
    exists x%:E; split; first by apply/real_total_integrand_graph.
    by rewrite -EFinN.
have hNegOpp':=measure_integral_graph_equivalent he hNegOpp.
have hEq:a=(-a)%E:=measure_integral_unique hNegSame hNegOpp'.
clear hNegOpp' hNegOpp hNegSame hTransport.
case:a ha hEq=>[r| |] hi heq.
- apply:(@scalar_identity_not_summable R); by exists r.
- discriminate heq.
- discriminate heq.
Qed.
