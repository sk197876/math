(** Federer (1969), 4.1.8, p. 362: the original
    scalar integral on [0,1] is exactly integration over
    its actual compact relative carrier. Use only the
    original subspace image law and 2.4.10 and 2.4.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology CurrentSegmentParameter
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureRestriction MeasurePushforward OpenSubspaceMeasure
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  RestrictedIntegralIdentity InjectivePushforwardIntegral SummableRealFunctionUP
  LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSegmentParameterIntegral.
Variable R:realType.
Local Notation Q := (current_segment_parameter R).
Local Notation Leb := (@lebesgue_scalar_measure R).
Local Notation mu := (@current_segment_parameter_measure R).
Local Notation hm := (@current_segment_parameter_is_measure R).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [current_segment_parameter_integral_iff]: the
    original interval integral and the actual parameter
    integral have identical values and definedness, supporting
    Federer 4.1.8, p. 362. No continuity premise is needed. *)
Theorem current_segment_parameter_integral_iff (f:R->R) a:
  is_measure_subset_integral Leb I (real_total_integrand f) a <->
  is_measure_integral mu (real_total_integrand (fun t:Q=>f (set_val t))) a.
Proof.
have hI:measure_measurable Leb I.
  apply:(borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact:closed_borel_set (@segment_closed_real R 0 1).
have hPush:measure_pushforward (fun t:Q=>(set_val t:real_line_metric R)) mu= measure_restrict Leb I.
  exact:(@open_subspace_measure_pushforward R (real_line_metric R) I Leb).
have hInjective:injective (fun t:Q=>(set_val t:real_line_metric R)).
  move=>t u;exact:val_inj.
have hGraph t z:partial_function_graph
    (partial_function_precompose (fun t:Q=>(set_val t:real_line_metric R)) (real_total_integrand f)) t z <->
    partial_function_graph (real_total_integrand (fun t:Q=>f (set_val t))) t z.
  change (partial_function_graph (real_total_integrand f) (set_val t) z <->
    partial_function_graph (real_total_integrand (fun t:Q=>f (set_val t))) t z).
  by rewrite !real_total_integrand_graph.
split=>hIntegral.
- have hRestricted:=(@restricted_integral_zero_extension_iff R (real_line_metric R)
    Leb (lebesgue_scalar_is_measure R) I (real_total_integrand f) a hI).2 hIntegral.
  rewrite -hPush in hRestricted.
  have hActual:=(@injective_pushforward_integral_iff R Q (real_line_metric R) mu hm
    (fun t:Q=>(set_val t:real_line_metric R)) (real_total_integrand f) hInjective a).2 hRestricted.
  exact:(measure_integral_graph_equivalent hGraph hActual).
- have hActual:=@measure_integral_graph_equivalent R Q mu _ _ a
    (fun t z=>iff_sym (hGraph t z)) hIntegral.
  have hRestricted:=(@injective_pushforward_integral_iff R Q (real_line_metric R) mu hm
    (fun t:Q=>(set_val t:real_line_metric R)) (real_total_integrand f) hInjective a).1 hActual.
  rewrite hPush in hRestricted.
  exact:(@restricted_integral_zero_extension_iff R (real_line_metric R)
    Leb (lebesgue_scalar_is_measure R) I (real_total_integrand f) a hI).1 hRestricted.
Qed.
End CurrentSegmentParameterIntegral.
