(** Federer (1969), 2.4.4(2),(5), p. 82:
    measurable nonnegative functions admit genuine integrals,
    and pointwise two-sided bounds compare those integrals.
    This supports the actual fibre comparison in 3.2.46,
    p. 282, including zero and infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralBounds MeasureNonnegativeIntegral MeasureIntegralComparison MeasureIntegralScaleLaw
  MeasureUpperIntegralScale ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_integral_two_sided_bounds]:
    two applications of integral monotonicity in the
    local fibre argument of 3.2.46, p. 282,
    using 2.4.4(2),(5), p. 82. Integral
    existence of the first original function is proved
    from measurability and nonnegativity; no finiteness
    or independently supplied integrability is required. *)
Lemma nonnegative_integral_two_sided_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (p q : X -> extended_real_line R) (c : R) b :
  is_measure mu -> 0<c -> (forall x, (0<=p x)%E) ->
  is_measure_measurable_function mu (partial_function_total p) ->
  is_measure_integral mu (partial_function_total q) b ->
  (forall x, (p x<=c%:E*q x)%E /\ (q x<=c%:E* p x)%E) ->
  exists a, (0<=a)%E /\ is_measure_integral mu (partial_function_total p) a /\
    (a<=c%:E*b)%E /\ (b<=c%:E*a)%E.
Proof.
move=> hMu hc hp hMeas hQ hBounds.
have hPos : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total p)).
  apply:(@measure_almost_everywhere_mono R X mu hMu classical_sets.setT _ _
    (measure_almost_everywhere_true hMu))=> x _.
  exists (p x); by split.
have [hP ha] := @nonnegative_measurable_function_integral R X mu hMu
  (partial_function_total p) hMeas hPos.
exists (measure_lower_integral mu (partial_function_total p)); split; first exact ha.
split; first exact hP; split.
- have hScaled := measure_integral_positive_scale hMu hc hQ.
  apply:(measure_integral_monotone hMu hP hScaled).
  apply:(@measure_almost_everywhere_mono R X mu hMu classical_sets.setT _ _
    (measure_almost_everywhere_true hMu))=> x _.
  exists (p x),(c%:E*q x)%E; split; first by [].
  split; first by exists (q x); split.
  exact:(hBounds x).1.
- have hScaled := measure_integral_positive_scale hMu hc hP.
  apply:(measure_integral_monotone hMu hQ hScaled).
  apply:(@measure_almost_everywhere_mono R X mu hMu classical_sets.setT _ _
    (measure_almost_everywhere_true hMu))=> x _.
  exists (q x),(c%:E* p x)%E; split; first by [].
  split; first by exists (p x); split.
  exact:(hBounds x).2.
Qed.
