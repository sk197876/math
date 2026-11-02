(** Federer (1969), 2.4.14, p. 88: sufficiency of equal or opposite
    normalised signed powers. The unit powered integrals and the sign
    relation give signed product integral one or minus one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialNormProduct
  PartialScalarProduct PartialSignedPower PartialAbsolutePartsGraph
  MeasureYoungEquality MeasureSignedPowerConverse MeasureSignedAbsoluteRecovery
  MeasureUP MeasureAlmostUP MeasureIntegralUP MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_unit_equal_signed_integral]: positive-sign
    sufficiency in the normalised equality proof of Federer 2.4.14, p. 88 *)
Lemma measure_holder_unit_equal_signed_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) p f) 1 ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) q g) 1 ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q 1%R f g) ->
  is_measure_integral mu (partial_scalar_product f g) 1.
Proof.
move=> hp hq hpq hfi hgi he.
have [hpow hsign] := @almost_equal_signed_powers_absolute_and_sign R X mu hm p q f g hp hq he.
have hprod := @measure_young_equal_powers_unit_integral R X R^o R^o
  (fun x : R => `|x|%R) (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
  mu hm p q f g hp hq hpq hfi hgi hpow.
have habs : is_measure_integral mu (partial_extended_function_absolute_value (partial_scalar_product f g)) 1.
  apply: (@measure_integral_graph_equivalent R X mu _ _ 1 _ hprod)=> x z.
  exact (iff_sym (partial_scalar_absolute_product_graph f g x z)).
exact (@nonnegative_absolute_integral_recovers R X mu hm _ 1 habs hsign).
Qed.

(** Source for [measure_holder_unit_opposite_signed_integral]: negative-sign
    sufficiency in the normalised equality proof of Federer 2.4.14, p. 88 *)
Lemma measure_holder_unit_opposite_signed_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) p f) 1 ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) q g) 1 ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q (-1)%R f g) ->
  is_measure_integral mu (partial_scalar_product f g) (-1).
Proof.
move=> hp hq hpq hfi hgi he.
have [hpow hsign] := @almost_opposite_signed_powers_absolute_and_sign R X mu hm p q f g hp hq he.
have hprod := @measure_young_equal_powers_unit_integral R X R^o R^o
  (fun x : R => `|x|%R) (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
  mu hm p q f g hp hq hpq hfi hgi hpow.
have habs : is_measure_integral mu (partial_extended_function_absolute_value (partial_scalar_product f g)) 1.
  apply: (@measure_integral_graph_equivalent R X mu _ _ 1 _ hprod)=> x z.
  exact (iff_sym (partial_scalar_absolute_product_graph f g x z)).
exact (@nonpositive_absolute_integral_recovers R X mu hm _ 1 habs hsign).
Qed.
