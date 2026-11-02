(** Federer (1969), 3.1.4, pp. 214–215: a measurable real
    representative of the scalar partial derivative on its domain.
    Values outside that domain are auxiliary only; the sealed derivative
    remains partial and is never redefined there. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RealNormUP NormMetric RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  PartialZeroExtension PartialFunctionExtensionUP ApproximatePartialDerivative
  ScalarApproximatePartialMeasurable ScalarNormExtendedEmbedding
  MeasureUP MeasurableFunctionUP RestrictedFunctionMeasurability
  MeasurablePostcomposition BorelFunctionBasic MeasurableTotalExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [measurable_approximate_partial_representative]: the
    use of the real values g_i on A_i in Federer 3.1.4,
    pp. 214–215. The auxiliary total representative follows from
    2.3.2 and the zero extension 2.4.10. No derivative value is
    asserted off its actual domain. *)
Theorem measurable_approximate_partial_representative (R : realType) m (i : 'I_m)
    (A : set (R_n R m)) (f : R_n R m -> R^o) :
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_source_restrict A (partial_function_total f)) ->
  exists g : R_n R m -> R^o,
    @is_measure_measurable_function R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
      [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
      (partial_function_total g) /\
    forall x c, partial_function_graph
      (approximate_partial_derivative (scalar_absolute_value_norm R) A f i) x c -> g x=c.
Proof.
move=> hf.
pose hm := euclidean_lebesgue_is_measure R m.
pose D := approximate_partial_derivative (scalar_absolute_value_norm R) A f i.
have hA := @approximate_partial_scalar_domain_measurable R m i A f hf.
have hD := @approximate_partial_scalar_measurable R m i A f hf.
have hZ := restricted_measurable_zero_extension hm
  (0 : real_norm_metric_space (scalar_absolute_value_norm R)) hA hD.
have hZr := measurable_function_borel_postcomposition hm hZ
  (continuous_borel_function (@scalar_norm_real_identity_continuous R)).
have [g [hge [_ hgm]]] := measurable_function_total_extension hm (0 : real_line_metric R) hZr.
exists g; split=> // x c hc.
apply: hge; exists c; split=> //.
apply: (@partial_function_zero_extension_on (R_n R m) (real_norm_metric_space (scalar_absolute_value_norm R)) 0
  (partial_function_domain D) D x c _).2=> //.
by exists c.
Qed.
