(** Federer (1969), 4.1.9, pp. 363–364: the
    literal time subset integral agrees with integration
    on its original relative compact parameter carrier.
    This supports the Fubini expression for the homotopy
    weight, retaining actual partial domains and infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground CurrentSegmentParameter ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasureRestriction MeasurePushforward
  OpenSubspaceMeasure RestrictedIntegralIdentity InjectivePushforwardIntegral MeasureIntegralUP MeasureSubsetIntegral
  LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_segment_partial_integral_iff]: the
    original [0,1] time integral and relative parameter
    integral have identical definedness and value for
    every original partial extended-real integrand, supporting
    Federer 4.1.9, pp. 363–364, by 2.4.10 and
    2.4.18. This extends the already proved real-valued adapter. *)
Theorem current_segment_partial_integral_iff (R:realType)
    (f:partial_function (real_line_metric R) (extended_real_line R)) a:
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R)) f a <->
  is_measure_integral (@current_segment_parameter_measure R)
    (partial_function_precompose (fun t:current_segment_parameter R=>(set_val t:real_line_metric R)) f) a.
Proof.
pose I:=(`[0,1]:set (real_line_metric R)).
have hI:measure_measurable (@lebesgue_scalar_measure R) I.
  apply:(borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact:closed_borel_set (@segment_closed_real R 0 1).
have hPush:measure_pushforward (fun t:current_segment_parameter R=>(set_val t:real_line_metric R))
    (@current_segment_parameter_measure R)=measure_restrict (@lebesgue_scalar_measure R) I.
  exact:(@open_subspace_measure_pushforward R (real_line_metric R) I (@lebesgue_scalar_measure R)).
have hInjective:injective (fun t:current_segment_parameter R=>(set_val t:real_line_metric R)).
  move=>t u;exact:val_inj.
have hTransport:=@injective_pushforward_integral_iff R (current_segment_parameter R) (real_line_metric R)
  (@current_segment_parameter_measure R) (@current_segment_parameter_is_measure R)
  (fun t:current_segment_parameter R=>(set_val t:real_line_metric R)) f hInjective a.
rewrite hPush in hTransport.
exact:(iff_trans (iff_sym (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_is_measure R) I f a hI)) (iff_sym hTransport)).
Qed.
