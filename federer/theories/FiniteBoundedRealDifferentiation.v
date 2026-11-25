(** Federer (1969), 4.1.5, p. 350:
    apply 2.9.8 to a bounded scalar dual
    evaluation after a finite-measure localization.
    The absolute local integrability is proved
    from the finite mass and original scalar bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAbsolute MeasureAlmostUP
  MeasureSubsetIntegral MeasurableFunctionUP SummableRealFunctionUP SummableRealArithmetic
  FiniteMeasureBoundedNorm VectorDaniellPairingMeasurability SummableSubsetRestriction
  LocalAbsoluteIntegrability MeasureDerivationContext CoveringRelationUP CoveringRelationLimits
  MeasureMeanFunction MeasureDifferentiation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_bounded_real_locally_absolutely_integrable]:
    the local integrability required for the
    scalar evaluations in Federer 4.1.5, p. 350,
    derived from the finite localized mass. *)
Lemma finite_bounded_real_locally_absolutely_integrable (R:realType) (X:metricType R)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->R) (M:R):
  (mu setT< +oo)%E ->is_measure_measurable_function mu (real_total_integrand f) ->
  (forall x,`|f x|<=M) ->
  is_locally_absolutely_integrable mu (real_total_integrand f).
Proof.
move=>hFinite hF hBound.
have hMassFinite:mu setT \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm setT)).
have hMass:mu setT=(fine (mu setT))%:E by rewrite fineK.
have hConstant:=@finite_measure_constant_integral R X mu hm (fine (mu setT)) M hMass.
have hConstantReal:is_measure_integral mu (real_total_integrand (fun _:X=>M))
    (M*fine (mu setT))%:E.
  apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hConstant)=>x z.
  change (M%:E=z <->partial_function_graph (real_total_integrand (fun _:X=>M)) x z).
  by rewrite real_total_integrand_graph.
have[c [hC _]]:=@real_total_dominated_integral R X mu hm f (fun _=>M)
  (M*fine (mu setT)) hF hConstantReal hBound.
have hAbsolute:=@measure_summable_absolute_value R X mu hm _ (ex_intro _ c hC).
move=>A _ hA.
exact:(@summable_measurable_zero_extension R X mu hm A _ hA hAbsolute).
Qed.

(** Source for [finite_bounded_real_differentiation]: the
    original scalar integral-mean differentiation
    of 2.9.8 applied in Federer 4.1.5,
    p. 350. Undefined quotients retain their
    original partial graph. *)
Theorem finite_bounded_real_differentiation (R:realType) (X:metricType R)
    (mu:set X->\bar R) (V:X->set X->Prop) (f:X->R) (M:R):
  is_measure_derivation_context mu V ->(mu setT< +oo)%E ->
  is_measure_measurable_function mu (real_total_integrand f) ->
  (forall x,`|f x|<=M) ->
  measure_almost_equal mu (covering_relation_limit V (measure_mean_function mu (real_total_integrand f)))
    (real_total_integrand f).
Proof.
move=>hContext hFinite hF hBound.
have hm:=derivation_measure_law (derivation_context_measure hContext).
exact:(@federer_2_9_8 R X mu V (real_total_integrand f) hContext hF
  (finite_bounded_real_locally_absolutely_integrable hm hFinite hF hBound)).
Qed.
