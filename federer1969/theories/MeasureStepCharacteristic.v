(** Federer (1969), proof of 2.4.4(2), p. 83: characteristic functions of
    measurable sets provide lower step functions in the infinite-value case.
    Their assigned sum is the measure of the set, by the definition of a
    step sum. This supports 2.4.4 and anticipates only the measurable-set
    case of 2.4.5, not its outer-integral assertions. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic CharacteristicFunctionUP MeasurableFunctionUP MeasurableTotalPiecewise
  MeasurableTotalBasic MeasureStepFunctionUP NumericalSumSingleSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_total_characteristic_function]:
    supporting measurability of the lower-function building block
    in Federer 2.4.4(2), p. 83. *)
Lemma measurable_total_characteristic_function (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s -> measure_measurable mu A ->
  is_measure_measurable_function mu (partial_function_total s).
Proof.
move=> hs hA.
have he : s = (fun x => if pselect (A x) then (1%R : real_line_metric R) else 0%R).
  apply: funext=> x; case: (pselect (A x))=> hx.
  - exact (@characteristic_on_set R X A s hs x hx).
  - exact (@characteristic_off_set R X A s hs x hx).
rewrite he; apply: (@measurable_total_piecewise R X [the topologicalType of real_line_metric R]
  mu hm A (fun _ => 1%R) (fun _ => 0%R) hA); exact: measurable_total_constant.
Qed.

(** Source for [characteristic_step_range_countable]: the two-
    point range of the characteristic lower functions in Federer
    2.4.4(2), p. 83. *)
Lemma characteristic_step_range_countable (R : realType) (X : Type) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s -> countable (partial_function_range (partial_function_total s)).
Proof.
move=> hs; pose v (b : bool) : R := if b then 1%R else 0%R.
have hi : partial_function_range (partial_function_total s) `<=` v @` setT.
  move=> y [x hx]; have [ha|ha] := pselect (A x).
  - exists true=> //; by rewrite /v -(hx : s x=y) (characteristic_on_set hs ha).
  - exists false=> //; by rewrite /v -(hx : s x=y) (characteristic_off_set hs ha).
apply: sub_countable (subset_card_le hi) _.
apply: sub_countable (card_image_le v _) _; exact: countableP.
Qed.

(** Source for [characteristic_step_assigned_sum]: the assigned
    sum for the characteristic lower functions in Federer
    2.4.4(2), p. 83, is mu(A), even when infinite. *)
Lemma characteristic_step_assigned_sum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s ->
  is_measure_step_integral mu (partial_function_total s) (mu A).
Proof.
move=> hs; pose u := partial_function_total s.
have h1 : partial_function_preimage u [set 1%R] = A.
  apply/seteqP; split=> x.
  - move=> [y [hy he]]; apply: contrapT=> hx.
    have hh := characteristic_off_set hs hx.
    have hb : (0%R : R) = 1%R by rewrite -hh hy.
    by move: hb=> /eqP; rewrite eq_sym oner_eq0.
  - move=> hx; exists 1%R; split=> //; exact (@characteristic_on_set R X A s hs x hx).
have hz y : (@setT R) y -> y != 1%R -> y%:E*mu (partial_function_preimage u [set y]) = 0.
  move=> _ hy; have [hy0|hy0] := eqVneq y 0%R; first by rewrite hy0 mul0e.
  have he : partial_function_preimage u [set y] = set0.
    apply/seteqP; split=> x; last by case.
    move=> [z [hz hzy]]; have [hx|hx] := pselect (A x).
    + apply: (negP hy); apply/eqP; by rewrite -hzy -(hz : s x=z) (characteristic_on_set hs hx).
    + apply: (negP hy0); apply/eqP; by rewrite -hzy -(hz : s x=z) (characteristic_off_set hs hx).
  by rewrite he (measure_empty hm) mule0.
rewrite /is_measure_step_integral (@numerical_sum_single_support R R setT _ 1%R Logic.I hz).
by rewrite h1 mul1e.
Qed.

(** Source for [measure_characteristic_step_function]: the
    characteristic functions used in the first case of Federer
    2.4.4(2), p. 83, satisfy all step-function laws. *)
Lemma measure_characteristic_step_function (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s -> measure_measurable mu A ->
  is_measure_step_function mu (partial_function_total s).
Proof.
move=> hs hA; constructor.
- exact (@measurable_total_characteristic_function R X mu hm A s hs hA).
- exact: characteristic_step_range_countable hs.
- exists (mu A); exact (@characteristic_step_assigned_sum R X mu hm A s hs).
Qed.
