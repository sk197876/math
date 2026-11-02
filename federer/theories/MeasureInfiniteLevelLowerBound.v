(** Federer (1969), first case in the proof of 2.4.4(2), p. 83: n times the
    characteristic function of f^{-1}{infinity} is a lower step function for
    almost-everywhere nonnegative f. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedArithmeticDomains
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableFunctionBorel CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureStepFunctionUP MeasureStepCharacteristic MeasureStepScalarOperation MeasureStepScaling
  MeasureIntegralUP MeasureIntegralBounds PartialExtendedOrderLoci ExtendedNaturalMultiples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_function_infinite_level_lower_bound]:
    the displayed lower-integral bound in the proof of Federer
    2.4.4(2), p. 83, for every natural multiplier. *)
Lemma nonnegative_function_infinite_level_lower_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) n :
  is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  n%:R%:E * mu (partial_function_preimage f [set y | y == +oo]) <= measure_lower_integral mu f.
Proof.
move=> hf hp; pose A := partial_function_preimage f [set y | y == +oo].
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have hA : measure_measurable mu A.
  apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm f hf).
  exact: extended_order_singleton_borel.
have hu := @measure_characteristic_step_function R X mu hm A s hs hA.
have ha := @characteristic_step_assigned_sum R X mu hm A s hs.
have [hnu hna] := @measure_step_function_scale R X mu hm (partial_function_total s) n%:R (mu A) hu ha.
apply: (@measure_lower_integral_bound R X mu f _ _ _ hna); split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [z [hz hz0]]; exists (n%:R*s x)%R,z; split.
- exists (s x); by split.
- split=> //; have [hx|hx] := pselect (A x).
  + have [w [hw /eqP hwI]] := hx.
    have he := partial_function_single_valued hz hw; by rewrite he hwI leey.
  + have hs0 : s x = 0%R := characteristic_off_set hs hx.
    by rewrite hs0 mulr0.
Qed.

(** Source for [positive_infinite_level_lower_integral]: the
    first-case conclusion in Federer 2.4.4(2), p. 83:
    positive measure of the infinite level forces lower integral infinity. *)
Lemma positive_infinite_level_lower_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  0 < mu (partial_function_preimage f [set y | y == +oo]) -> measure_lower_integral mu f=+oo.
Proof.
move=> hf hp hA; apply: positive_natural_multiples_force_infinity hA _ => n.
exact (@nonnegative_function_infinite_level_lower_bound R X mu hm f n hf hp).
Qed.
