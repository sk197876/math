(** Federer (1969), 2.4.5, pp. 83–84: the lower integral of a characteristic
    function is at most the measure of the set. We use the positive
    variation of the assigned step sum and retain zero-measure fibres in
    that countable family. No measurability of A is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP
  MeasureStepFunctionUP MeasureStepFibres MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralBounds MeasureCharacteristicUpperBound
  MeasureAlmostSubsetBound MeasureStepFibreUnion ExtendedRealPartial
  NonnegativeSum NonnegativeSumRestriction NumericalSum NumericalSumOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_lower_step_high_fibre_null]: Supporting
    Federer 2.4.5, pp. 83–84. *)
Lemma characteristic_lower_step_high_fibre_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) (u : partial_function X (real_line_metric R)) y :
  is_characteristic_function A s ->
  measure_almost_everywhere mu
    (partial_step_lower_locus u (partial_real_function_embed (partial_function_total s))) ->
  (1 < y)%R -> mu (partial_function_preimage u [set y]) = 0.
Proof.
move=> hs huf hy.
apply: (@measure_null_subset R X mu hm _
  (~` partial_step_lower_locus u (partial_real_function_embed (partial_function_total s))) _ huf).
move=> x [v [hv ev]] [w [z [hw [[r [hr erz]] hwz]]]].
have evw := partial_function_single_valued hv hw.
have hry : (y <= r)%R by move: hwz; rewrite -evw ev -erz lee_fin.
have hr1 : (r <= 1)%R by rewrite -(hr : s x = r); exact: (andP (characteristic_function_scalar_bounds hs x)).2.
have hy1 := le_trans hry hr1.
by move: hy; rewrite ltNge hy1.
Qed.

(** Source for [measure_characteristic_lower_step_bound]: Supporting Federer
    2.4.5, pp. 83–84. *)
Lemma measure_characteristic_lower_step_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) (u : partial_function X (real_line_metric R)) a :
  is_characteristic_function A s ->
  is_measure_lower_function mu (partial_real_function_embed (partial_function_total s)) u ->
  is_measure_step_integral mu u a -> a <= mu A.
Proof.
move=> hs [hu huf] ha.
pose D := partial_function_range u `&` [set y : R | (0 < y <= 1)%R].
pose B := \bigcup_(y in D) partial_function_preimage u [set y].
pose c (y : R) := y%:E * mu (partial_function_preimage u [set y]).
pose p (y : R) := extended_positive_part (c y).
have hp y : (@setT R) y -> 0 <= p y by move=> _; exact: extended_positive_part_nonnegative.
have hap : a <= nonnegative_sum setT p.
  apply: (@numerical_sum_values_mono R R setT c p a (nonnegative_sum setT p))=> //.
  - by move=> y _; rewrite /p /extended_positive_part le_max lexx.
  - exact: numerical_sum_nonnegative hp.
have hc : countable D.
  apply: sub_countable (subset_card_le (fun y (hy : D y) => hy.1)) _.
  exact: step_function_countable_range hu.
have hBA : mu B <= mu A.
  apply: (@measure_almost_subset_bound R X mu hm B A).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huf).
  move=> x [y [z [hy [[w [hw hwz]] hyz]]]] [r [hr /andP[hr0 hr1]] [v [hv ev]]].
  have ery : r = y by rewrite -ev; exact: partial_function_single_valued hv hy.
  apply: contrapT=> hx.
  have hw0 : w = 0%R by rewrite -(hw : s x = w) (characteristic_off_set hs hx).
  have hrle : (r <= 0)%R by move: hyz; rewrite -hwz hw0 -ery lee_fin.
  by move: hr0; rewrite ltNge hrle.
have hz y : ~ D y -> p y = 0.
  move=> hy; have [hr|hr] := pselect (partial_function_range u y).
  - have [hy0|hy0] := ltP 0%R y.
    + have hy1 : (1 < y)%R.
        rewrite ltNge; apply/negP=> h; apply: hy; split=> //; by apply/andP.
      have he := @characteristic_lower_step_high_fibre_null R X mu hm A s u y hs huf hy1.
      by rewrite /p /c he mule0 /extended_positive_part maxxx.
    + rewrite /p /extended_positive_part max_r // /c.
      apply: mule_le0_ge0; first by rewrite lee_fin.
      exact: measure_nonnegative.
  - by rewrite /p /c (partial_fibre_outside_range hr) (measure_empty hm) mule0 /extended_positive_part maxxx.
have hzero : nonnegative_sum (setT `\` D) p = 0.
  apply: nonnegative_sum_zero=> y [_ hy]; exact: hz.
have hsplit : nonnegative_sum setT p = nonnegative_sum D p.
  by rewrite (@nonnegative_sum_split R R setT D p hp) setTI hzero adde0.
apply: le_trans hap _; rewrite hsplit.
apply: le_trans _ hBA.
rewrite -(@measure_selected_step_fibre_union R X mu hm u D (step_function_measurable hu) hc).
apply: nonnegative_sum_mono=> y [_ /andP[hy0 hy1]].
have hm0 := @measure_nonnegative R X mu hm (partial_function_preimage u [set y]).
have hc0 : 0 <= c y by apply: mule_ge0=> //; rewrite lee_fin; exact: ltW.
rewrite /p /extended_positive_part max_l // /c.
have hyE : y%:E <= (1 : \bar R) by rewrite lee_fin.
have hmul := @lee_wpmul2r R (mu (partial_function_preimage u [set y])) hm0 y%:E 1 hyE.
by rewrite mul1e in hmul.
Qed.

(** Source for [measure_characteristic_lower_bound]: direct
    first inequality in Federer 2.4.5, p. 84, taking
    the supremum of the lower step sums. *)
Theorem measure_characteristic_lower_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s ->
  measure_lower_integral mu (partial_real_function_embed (partial_function_total s)) <= mu A.
Proof.
move=> hs; apply: (measure_lower_integral_specification mu _).2=> a [u [hu ha]].
exact (@measure_characteristic_lower_step_bound R X mu hm A s u a hs hu ha).
Qed.
