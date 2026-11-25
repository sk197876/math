(** Federer (1969), 2.4.4(5), p. 82, proof p. 83: comparison of measurable
    functions includes integrability of both when either the upper function
    has integral below infinity or the lower function has integral above
    negative infinity. Our proof uses upper/lower monotonicity and the same
    finite-part criterion, a variation on Federer's subtraction argument
    that retains exact partial domains. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralNegation MeasureUpperIntegralMonotone
  MeasurableFiniteBoundIntegrable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lower_integral_monotone]: supporting
    dual bound comparison for Federer 2.4.4(5), pp. 82–83,
    obtained from 2.4.3(1)–(2) by negation. *)
Lemma measure_lower_integral_monotone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_le_locus f g) ->
  measure_lower_integral mu f <= measure_lower_integral mu g.
Proof.
move=> hfg.
have hn : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_negate g) (partial_extended_function_negate f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfg).
  move=> x [a [b [ha [hb hab]]]]; exists (-b),(-a); split.
  - exists b; by split.
  split; first by exists a; split.
  by rewrite leeN2.
rewrite !(@measure_lower_integral_negation R X mu hm) leeN2.
exact (@measure_upper_integral_monotone R X mu hm _ _ hn).
Qed.

(** Source for [measure_integral_monotone]: integrable-function
    special case of Federer 2.4.4(5), p. 82. Once
    both integrals exist no additional finite-side premise is needed. *)
Lemma measure_integral_monotone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) a b :
  is_measure_integral mu f a -> is_measure_integral mu g b ->
  measure_almost_everywhere mu (partial_extended_le_locus f g) -> a <= b.
Proof.
move=> hf hg hfg.
have ef := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hf.2.1.
have eg := @measure_upper_integral_unique R X mu g _ b (measure_upper_integral_specification mu g) hg.2.1.
rewrite -ef -eg; exact (@measure_upper_integral_monotone R X mu hm f g hfg).
Qed.

(** Source for [measurable_integral_comparison]: complete Federer 2.4.4(5),
    p. 82, making both integrability conclusions explicit. *)
Theorem measurable_integral_comparison (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_extended_le_locus f g) ->
  ((exists b, is_measure_integral mu g b /\ b < +oo) \/
   (exists a, is_measure_integral mu f a /\ -oo < a)) ->
  exists a b, is_measure_integral mu f a /\ is_measure_integral mu g b /\ a <= b.
Proof.
move=> hf hg hfg [[b [hb hfin]]|[a [ha hfin]]].
- have eg := @measure_upper_integral_unique R X mu g _ b (measure_upper_integral_specification mu g) hb.2.1.
  have huf : measure_upper_integral mu f < +oo.
    apply: le_lt_trans (@measure_upper_integral_monotone R X mu hm f g hfg) _.
    by rewrite eg.
  have [a ha] := @measurable_finite_upper_integrable R X mu hm f hf huf.
  exists a,b; split=> //; split=> //; exact (@measure_integral_monotone R X mu hm f g a b ha hb hfg).
- have ef := @measure_lower_integral_unique R X mu f _ a (measure_lower_integral_specification mu f) ha.2.2.
  have hlg : -oo < measure_lower_integral mu g.
    apply: lt_le_trans _ (@measure_lower_integral_monotone R X mu hm f g hfg).
    by rewrite ef.
  have [b hb] := @measurable_finite_lower_integrable R X mu hm g hg hlg.
  exists a,b; split=> //; split=> //; exact (@measure_integral_monotone R X mu hm f g a b ha hb hfg).
Qed.
