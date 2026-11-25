(** Federer (1969), 2.4.9, p. 85: fn-g and its absolute value are summable,
    and the absolute difference of the integrals is bounded by the integral
    of |fn-g|. These supporting consequences use 2.4.4(3), (4), (7), (8),
    pp. 82–83. Source context: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralNegationLaw MeasureIntegralAddition
  MeasureIntegralAbsolute PartialAbsolutePartsGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_finite_difference]: supporting
    difference integral used in the final inequality of Federer
    2.4.9, p. 85. Finiteness excludes undefined sums. *)
Lemma measure_integral_finite_difference (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) (a b : R) :
  is_measure_integral mu f a%:E -> is_measure_integral mu g b%:E ->
  is_measure_integral mu (partial_extended_function_subtract f g) (a-b)%:E.
Proof.
move=> hf hg.
have hn := @measure_integral_negation R X mu hm g b%:E hg.
apply: (@measure_integral_add R X mu hm f _ a%:E (-b%:E) (a-b)%:E hf hn).
by rewrite /extended_add /=.
Qed.

(** Source for [measure_summable_difference]: supporting summability of fn-g
    and |fn-g| in Federer 2.4.9, p. 85 *)
Lemma measure_summable_difference (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> is_measure_summable mu g ->
  is_measure_summable mu (partial_extended_function_subtract f g) /\
  is_measure_summable mu (partial_extended_function_absolute_value (partial_extended_function_subtract f g)).
Proof.
move=> [a ha] [b hb].
have hi := @measure_integral_finite_difference R X mu hm f g a b ha hb.
have hs : is_measure_summable mu (partial_extended_function_subtract f g) by exists (a-b)%R.
split=> //; exact (@measure_summable_absolute_value R X mu hm _ hs).
Qed.

(** Source for [measure_integral_difference_absolute_bound]:
    the final inequality in Federer 2.4.9, p. 85,
    as a scalar real bound once summability has been established. *)
Lemma measure_integral_difference_absolute_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) (a b e : R) :
  is_measure_integral mu f a%:E -> is_measure_integral mu g b%:E ->
  is_measure_integral mu (partial_extended_function_absolute_value (partial_extended_function_subtract f g)) e%:E ->
  (`|a-b| <= e)%R.
Proof.
move=> ha hb he.
have hi := @measure_integral_finite_difference R X mu hm f g a b ha hb.
have [d [hd hbound]] := @measure_integral_absolute_bound R X mu hm _ (a-b)%:E hi.
have ed := measure_integral_unique hd he; by rewrite ed in hbound.
Qed.
