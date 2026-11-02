(** Federer (1969), 2.4.12, pp. 86–87: the norm superlevel estimate and
    redundancy of countable measurability for finite p. The proofs use
    characteristic lower functions and the project's own integral laws; no
    external Markov or Lp theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureStepFunctionUP MeasureStepCharacteristic MeasureStepScalarOperation MeasureStepScaling
  MeasureIntegralUP MeasureIntegralBounds PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_threshold_lower_integral_bound]:
    characteristic-function comparison supporting the displayed
    superlevel estimate in Federer 2.4.12, p. 87.
    The coefficient may be zero and the measure infinite,
    with the book's zero-times-infinity convention. *)
Lemma nonnegative_threshold_lower_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (c : R)
    (f : partial_function X (extended_real_line R)) :
  measure_measurable mu A -> (0 <= c)%R ->
  (forall x, A x -> exists y, partial_function_graph f x y /\ c%:E <= y) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  c%:E * mu A <= measure_lower_integral mu f.
Proof.
move=> hA hc hAf hp; pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have hu := @measure_characteristic_step_function R X mu hm A s hs hA.
have ha := @characteristic_step_assigned_sum R X mu hm A s hs.
have [hcu hca] := @measure_step_function_scale R X mu hm (partial_function_total s) c (mu A) hu ha.
apply: (@measure_lower_integral_bound R X mu f _ _ _ hca); split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [z [hz hz0]]; exists (c*s x)%R,z; split.
- exists (s x); by split.
- split=> //; have [hx|hx] := pselect (A x).
  + have [y [hy hcy]] := hAf x hx.
    have he := partial_function_single_valued hy hz.
    by rewrite /s (characteristic_on_set hs hx) mulr1 -he.
  + by rewrite /s (characteristic_off_set hs hx) mulr0.
Qed.
