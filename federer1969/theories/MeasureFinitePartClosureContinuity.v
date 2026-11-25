(** Federer (1969), 2.4.17, p. 90: continuity on the closure, first for the
    finite part of P. This theorem uses a sealed countable base and the
    proved general topology criterion to obtain full subspace continuity,
    including values at every closure point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasureExponentDomain FiniteExponentPart ExtendedRealOrderTopology
  ExtendedRealCountableBaseSealed CountableBaseSequentialLimit ExtendedClosedNeighborhoods
  RelativeLimitClosureContinuity MeasureExponentFinitePartLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_norm_continuous_on_finite_part_closure]: the
    closure-continuity assertion of Federer 2.4.17, p. 90, on Closure(P
    intersect R). The possible isolated infinity exponent is treated
    separately when replacing this closure by Closure P. *)
Theorem measure_norm_continuous_on_finite_part_closure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  continuous (fun p : subspace (closure (finite_exponent_part
      (measure_finite_norm_exponents mu (partial_function_total f)))) =>
    (measure_exponent_norm mu (partial_function_total f) p : extended_real_line R)).
Proof.
move=> hf; apply: relative_limits_continuous_on_closure.
- exact: extended_real_closed_neighborhood_refinement.
- move=> p hp; apply: (@countable_base_sequential_relative_limit (extended_real_line R) (extended_real_line R)
    (@ExtendedRealCountableBase.value R) (@ExtendedRealCountableBase.laws R)).
  move=> u hu hl.
  exact: (@measure_exponent_finite_part_sequential_limit R X mu hm f hf u p hu hl).
Qed.
