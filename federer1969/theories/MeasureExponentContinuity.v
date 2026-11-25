(** Federer (1969), 2.4.17, p. 90: the map p |-> phi_p(f) is continuous on
    Closure P in the extended real line. This final assembly includes empty
    P and the singleton infinity case. The explicit countable base and
    closure-limit arguments supply general topology only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasureExponentDomain ExtendedRealOrderTopology ExtendedExponentInterval FiniteExponentPart
  ExtendedIntervalFiniteDensity ExtendedInfinitySingletonContinuity MeasureFinitePartClosureContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_exponent_norm_continuous_on_closure]: the complete
    continuity assertion of Federer 2.4.17, p. 90 Both domain and codomain
    use the project's extended-real order topology. The restriction is to
    Closure P, including infinite-norm endpoints, rather than only the
    finite-norm exponents themselves. *)
Theorem measure_exponent_norm_continuous_on_closure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  continuous (fun p : subspace (closure
      (measure_finite_norm_exponents mu (partial_function_total f) : set (extended_real_line R))) =>
    (measure_exponent_norm mu (partial_function_total f) p : extended_real_line R)).
Proof.
move=> hf.
pose P := measure_finite_norm_exponents mu (partial_function_total f).
have hdom p : P p -> 1 <= p by move=> hp; exact hp.1.
have [hreal|hreal] := pselect (exists s : R, P s%:E).
- have [s hs] := hreal.
  have hP := @measure_finite_norm_exponents_interval R X mu hm (partial_function_total f) hf.
  have he := @extended_interval_finite_part_closure R P s hP hdom hs.
  have hh := @measure_norm_continuous_on_finite_part_closure R X mu hm f hf.
  by rewrite -/P he in hh.
- apply: infinity_supported_closure_continuous=> p hp.
  case: p hp=> [p| |] hp.
  + exfalso; apply: hreal; by exists p.
  + by [].
  + have hh := hdom -oo hp; by move: hh; rewrite leNgt ltNyr.
Qed.
