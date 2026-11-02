(** Federer (1969), 2.4.5, pp. 83–84: the measure of an arbitrary set is at
    most the upper integral of its characteristic function. We retain all
    such fibres in the countable range; zero-measure fibres contribute zero,
    so need not be removed separately. No measurability of A is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP
  MeasureStepFunctionUP MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralBounds MeasureStepNonnegative
  MeasureAlmostSubsetBound MeasureStepFibreUnion NonnegativeSum NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_function_scalar_bounds]: supporting
    zero-to-one range bounds in Federer 2.4.5, pp. 83–84;
    derived from the abstract characteristic-function laws. *)
Lemma characteristic_function_scalar_bounds (R : realType) (X : Type)
    (A : set X) (s : X -> R) :
  is_characteristic_function A s -> forall x, (0 <= s x <= 1)%R.
Proof.
move=> hs x; have [hx|hx] := pselect (A x).
- by rewrite (characteristic_on_set hs hx) ler01 lexx.
- by rewrite (characteristic_off_set hs hx) lexx ler01.
Qed.

(** Source for [measure_characteristic_upper_step_bound]: Supporting Federer
    2.4.5, pp. 83–84. *)
Lemma measure_characteristic_upper_step_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) (u : partial_function X (real_line_metric R)) a :
  is_characteristic_function A s ->
  is_measure_upper_function mu (partial_real_function_embed (partial_function_total s)) u ->
  is_measure_step_integral mu u a -> mu A <= a.
Proof.
move=> hs [hu huf] ha.
pose D := partial_function_range u `&` [set y : R | (1 <= y)%R].
pose B := \bigcup_(y in D) partial_function_preimage u [set y].
have hc : countable D.
  apply: sub_countable (subset_card_le (fun y (hy : D y) => hy.1)) _.
  exact: step_function_countable_range hu.
have hAB : mu A <= mu B.
  apply: (@measure_almost_subset_bound R X mu hm A B).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huf).
  move=> x [y [z [hy [[w [hw hwz]] hzy]]]] hx.
  have hw1 : w = 1%R by rewrite -(hw : s x = w) (characteristic_on_set hs hx).
  have hy1 : (1 <= y)%R by move: hzy; rewrite -hwz hw1 lee_fin.
  exists y.
  - split; [by exists x|exact hy1].
  - exists y; by split.
have hpos : measure_almost_everywhere mu (partial_real_nonnegative_locus u).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huf).
  move=> x [y [z [hy [[w [hw hwz]] hzy]]]].
  exists y; split=> //.
  have hw0 : (0 <= w)%R by rewrite -(hw : s x = w); exact: (andP (characteristic_function_scalar_bounds hs x)).1.
  move: hzy; rewrite -hwz lee_fin=> hwy; exact: le_trans hw0 hwy.
have hp y : (@setT R) y -> 0 <= y%:E * mu (partial_function_preimage u [set y]).
  move=> _; exact (@measure_step_nonnegative_coefficients R X mu hm u hpos y).
rewrite /is_measure_step_integral (numerical_sum_nonnegative hp) in ha.
case: ha=> <-; apply: le_trans hAB _.
rewrite -(@measure_selected_step_fibre_union R X mu hm u D (step_function_measurable hu) hc).
apply: le_trans _ (@nonnegative_sum_subset R R D setT
  (fun y => y%:E * mu (partial_function_preimage u [set y])) (fun _ _ => Logic.I)).
apply: nonnegative_sum_mono=> y [_ hy].
have he : (1 : \bar R) <= y%:E by rewrite lee_fin.
have hz := @measure_nonnegative R X mu hm (partial_function_preimage u [set y]).
exact: lee_pemull hz he.
Qed.

(** Source for [measure_characteristic_upper_bound]: direct
    second inequality in Federer 2.4.5, p. 84, taking
    the infimum of the upper step sums. *)
Theorem measure_characteristic_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s ->
  mu A <= measure_upper_integral mu (partial_real_function_embed (partial_function_total s)).
Proof.
move=> hs; apply: (measure_upper_integral_specification mu _).2=> a [u [hu ha]].
exact (@measure_characteristic_upper_step_bound R X mu hm A s u a hs hu ha).
Qed.
