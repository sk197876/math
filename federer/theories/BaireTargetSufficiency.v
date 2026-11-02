(** Federer (1969), 2.2.15, p. 71, sufficiency of the final target
    criterion. The source may be any metric space; the target is separable.
    Finite-curve approximation makes every countable Borel step map Baire.
    The sealed countable approximants then converge to the given Borel map.
    This supplies the proof omitted in the book. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground BorelFunctionUP BaireFunctions
  FiniteCurveApproximationUP CountableBorelApproximationUP CountableBorelApproximationSealed
  CountableBorelApproximationLimit CountableBorelStepsBaire.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [borel_baire_target_sufficient]: direct sufficiency
    in Federer 2.2.15, p. 71. The curve condition
    itself supplies a target point; separability supplies the
    countable approximation. No completeness is assumed. *)
Theorem borel_baire_target_sufficient (R : realType) (Y : metricType R)
    (D : set Y) : countable D -> dense D -> has_finite_curve_approximation Y ->
  forall (X : metricType R) (f : X -> Y), is_borel_function f -> is_baire_function f.
Proof.
move=> hc hd h X f hf.
have [c _] := h set0 (@finite_set0 Y) 1 (@Num.Theory.ltr01 R).
pose y0 := c 0.
pose w := @CountableBorelApproximation.value R X Y f y0 D hc hd hf.
have hw := @CountableBorelApproximation.laws R X Y f y0 D hc hd hf.
apply: (@baire_function_pointwise_limit R X Y (fun k => w.1 \o w.2 k) f).
- move=> k; exact: countable_borel_step_baire h (countable_approximation_fibres hw k).
- exact: countable_borel_approximations_converge hw.
Qed.
