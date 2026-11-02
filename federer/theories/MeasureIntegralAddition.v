(** Federer (1969), 2.4.4(4), p. 82, proof p. 83: addition of integrable
    functions when their extended integral sum is defined. The printed
    condition allows positive and negative infinity; it excludes only
    opposite infinities. The three proof cases are retained. Source
    editions: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic
  MeasureUP MeasureAlmostUP MeasurableExtendedArithmetic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralSqueeze MeasureUpperIntegralSubadditive MeasureLowerIntegralSuperadditive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_add]: direct Federer
    2.4.4(4), p. 82, including integrability of the
    partial pointwise sum and both same-sign infinite outcomes. *)
Theorem measure_integral_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) a b z :
  is_measure_integral mu f a -> is_measure_integral mu g b -> extended_add a b=Some z ->
  is_measure_integral mu (partial_extended_function_add f g) z.
Proof.
move=> [hf [hfu hfl]] [hg [hgu hgl]] hz.
have eu := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hfu.
have ev := @measure_upper_integral_unique R X mu g _ b (measure_upper_integral_specification mu g) hgu.
have el := @measure_lower_integral_unique R X mu f _ a (measure_lower_integral_specification mu f) hfl.
have em := @measure_lower_integral_unique R X mu g _ b (measure_lower_integral_specification mu g) hgl.
have hupper : extended_add (measure_upper_integral mu f) (measure_upper_integral mu g)=Some z by rewrite eu ev.
have hlower : extended_add (measure_lower_integral mu f) (measure_lower_integral mu g)=Some z by rewrite el em.
case: z hz hupper hlower=> [r| |] hz hupper hlower.
- have [hd hu] := @measure_upper_integral_sum_consequences R X mu hm f g r%:E hupper (ltry r).
  have [_ hl] := @measure_lower_integral_sum_consequences R X mu hm f g r%:E hlower (ltNyr r).
  apply: (@measure_integral_squeeze R X mu hm _ _ _ hu hl).
  exact (@measurable_extended_function_add R X mu hm f g hf hg hd).
- have hpos : (-oo : \bar R) < +oo by [].
  have [hd hl] := @measure_lower_integral_sum_consequences R X mu hm f g +oo hlower hpos.
  apply: (@measure_integral_squeeze R X mu hm _ _ _ (leey _) hl).
  exact (@measurable_extended_function_add R X mu hm f g hf hg hd).
- have hpos : (-oo : \bar R) < +oo by [].
  have [hd hu] := @measure_upper_integral_sum_consequences R X mu hm f g -oo hupper hpos.
  apply: (@measure_integral_squeeze R X mu hm _ _ _ hu (leNye _)).
  exact (@measurable_extended_function_add R X mu hm f g hf hg hd).
Qed.
