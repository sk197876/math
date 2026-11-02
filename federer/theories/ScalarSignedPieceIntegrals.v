(** Federer (1969), 3.2.6, p. 246: the
    original Lebesgue summability of g times total
    multiplicity supplies finite integrals on both actual
    derivative sign pieces. This uses the first identity
    and measurable restriction, exactly as in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ScalarAbsoluteContinuousArea
  ScalarCurveDerivativeLoci ScalarDerivativeSignMembership ScalarCurveRemainderNull LocallyAbsolutelyContinuousCurve
  PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws MeasureUP MeasureBasic MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableSubsetRestriction CoveringFamilyUP MetricDiameter LebesgueScalarMeasure
  IntervalBumpFunctions TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_area_source_subset_graph]: supporting
    restriction of the original source integrand to A_1
    and A_2 in Federer 3.2.6, p. 246. The nested
    subset cutoff preserves the exact partial derivative domain. *)
Lemma scalar_area_source_subset_graph (R:realType) (f g:R->R)
    (A B:set (real_line_metric R)):
  A `<=` B -> forall x z,
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (scalar_curve_area_source_integrand f B g)) x z <->
  partial_function_graph (scalar_curve_area_source_integrand f A g) x z.
Proof.
move=>hAB x z.
have he:A `&` B=A.
  apply/seteqP; split=>t; first by move=>[ht _].
  move=>ht; split=>//; exact (hAB t ht).
by rewrite /scalar_curve_area_source_integrand partial_zero_extension_intersection_graph he.
Qed.

(** Source for [scalar_signed_piece_finite_integrals]: the
    application of the first equation to the two sign
    sets in Federer 3.2.6, p. 246. Its hypothesis
    is precisely the corrected Lebesgue summability of
    g(y)N(f|[a,b],y), not measurability of g itself. *)
Theorem scalar_signed_piece_finite_integrals (R:realType) (f g:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> a<b ->
  is_measure_summable (@lebesgue_scalar_measure R) (scalar_curve_area_target_integrand f `[a,b] g) ->
  exists p q:R,
    is_measure_integral (@lebesgue_scalar_measure R)
      (scalar_curve_area_source_integrand f (scalar_positive_derivative_set f a b) g) p%:E /\
    is_measure_integral (@lebesgue_scalar_measure R)
      (scalar_curve_area_source_integrand f (scalar_negative_derivative_set f a b) g) q%:E /\
    is_measure_integral (@lebesgue_scalar_measure R)
      (scalar_curve_area_target_integrand f (scalar_positive_derivative_set f a b) g) p%:E /\
    is_measure_integral (@lebesgue_scalar_measure R)
      (scalar_curve_area_target_integrand f (scalar_negative_derivative_set f a b) g) q%:E.
Proof.
move=>hAC hab [i hi]; have hm:=lebesgue_scalar_is_measure R.
have hI:measure_measurable (@lebesgue_scalar_measure R) (`[a,b]:set (real_line_metric R)).
  exact (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R) _
    (closed_borel_set (@segment_closed_real R a b))).
have hBound:=real_metric_closed_interval_bounded (ltW hab).
have hSource:=(federer_3_2_6_1_scalar g hAC hBound hI i%:E).2 hi.
have hSum:is_measure_summable (@lebesgue_scalar_measure R) (scalar_curve_area_source_integrand f `[a,b] g).
  by exists i.
have hSets:=scalar_derivative_interval_sets_measurable a b hAC.
have hSub:=scalar_derivative_sign_sets_subinterval f a b.
have [p hP]:=summable_measurable_zero_extension hm hSets.1 hSum.
have [q hN]:=summable_measurable_zero_extension hm hSets.2.1 hSum.
have hPSource:=measure_integral_graph_equivalent (@scalar_area_source_subset_graph R f g _ _ hSub.1) hP.
have hNSource:=measure_integral_graph_equivalent (@scalar_area_source_subset_graph R f g _ _ hSub.2) hN.
have hPBound:metric_set_bounded (scalar_positive_derivative_set f a b).
  exact (le_lt_trans (extended_metric_diameter_mono hSub.1) hBound).
have hNBound:metric_set_bounded (scalar_negative_derivative_set f a b).
  exact (le_lt_trans (extended_metric_diameter_mono hSub.2) hBound).
exists p,q; split; first exact hPSource; split; first exact hNSource; split.
- exact ((federer_3_2_6_1_scalar g hAC hPBound hSets.1 p%:E).1 hPSource).
- exact ((federer_3_2_6_1_scalar g hAC hNBound hSets.2.1 q%:E).1 hNSource).
Qed.
