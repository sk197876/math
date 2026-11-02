(** Supporting cost-cover comparison for Federer (1969), 2.10.9, p. 175,
    from integral order 2.4.4(5), pp. 82–83, and the norm formulas 2.4.12,
    p. 86. Increasing a nonnegative extended input almost everywhere
    increases every admissible exponent norm, including infinity. No
    finite-value replacement is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower PartialFunctionBasic
  PartialExtendedOrderLoci MeasureUP MeasurableFunctionUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureNonnegativeLowerIntegral MeasureIntegralComparison
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_total_integral_value_ge0]: supporting
    integral nonnegativity from Federer 2.4.4(5), pp. 82–83,
    used in the norm cost comparison for 2.10.9, p. 175.
    The actual integral value is retained even when infinite. *)
Lemma nonnegative_total_integral_value_ge0 (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (a : \bar R) :
  (forall x, 0<=f x) -> is_measure_integral mu (partial_function_total f) a -> 0<=a.
Proof.
move=> hf hi.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _; exists (f x); by split.
have hn := @measure_lower_integral_nonnegative R X mu hm (partial_function_total f) hp.
by rewrite (@measure_lower_integral_unique R X mu (partial_function_total f) _ a
  (measure_lower_integral_specification mu _) hi.2.2) in hn.
Qed.

(** Source for [nonnegative_extended_norm_almost_order]: supporting
    norm comparison for the cost-cover hypothesis in Federer
    2.10.9, p. 175. It follows from 2.4.4(5), pp. 82–83,
    and 2.4.12, p. 86. The order premise holds almost
    everywhere; inputs, integrals and norms may be infinite. *)
Theorem nonnegative_extended_norm_almost_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> extended_real_line R) (t : \bar R) :
  (forall x, 0<=f x) -> (forall x, 0<=g x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_almost_everywhere mu [set x | f x<=g x] ->
  nonnegative_extended_exponent_norm mu f t<=nonnegative_extended_exponent_norm mu g t.
Proof.
move=> hf0 hg0 ht hf hg hfg.
have hF := @nonnegative_extended_exponent_norm_specification R X mu f t hm hf0 ht hf.
have hG := @nonnegative_extended_exponent_norm_specification R X mu g t hm hg0 ht hg.
case: t ht hF hG=> [p| |] ht hF hG; last by [].
- have [_ [a [hai heF]]] := hF.
  have [_ [b [hbi heG]]] := hG.
  have hp : (0<p)%R := lt_le_trans ltr01 ht.
  have hab : a<=b.
    apply: (@measure_integral_monotone R X mu hm _ _ a b hai hbi).
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfg)=> x hx.
    exists (extended_positive_power (f x) p), (extended_positive_power (g x) p).
    split=> //; split=> //; exact: extended_positive_power_monotone (hf0 x) hx hp.
  rewrite heF heG.
  apply: extended_positive_power_monotone _ hab _; last by rewrite invr_gt0.
  exact: (@nonnegative_total_integral_value_ge0 R X mu hm _ a
    (fun x => extended_positive_power_nonnegative (f x) p) hai).
- apply: hG.2=> r [hr hnull]; apply: hF.1; split=> //.
  apply: (@measure_null_subset R X mu hm _ _ _
    (@measure_null_union R X mu hm [set x | r<g x] (~` [set x | f x<=g x]) hnull hfg)).
  move=> x hx; case: (pselect (f x<=g x))=> [h|h]; last by right.
  left; exact: lt_le_trans hx h.
Qed.
