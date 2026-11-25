(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialExtendedArithmetic
  PartialZeroExtension PartialExtendedOrderLoci MeasurableDistanceTo
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableZeroExtension
  ZeroExtensionNonnegative CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureIntegralBounds MeasureSubsetIntegral MeasureIntegralAddition
  MeasureIntegralComparison MeasureIntegralUniqueness MeasureExtendedCharacteristicIntegral
  MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [distance_subset_integral_bound]: supporting finite local
    integrability and triangle bound in Federer 2.9.9, pp. 156–157. at
    exponent one, the triangle inequality and addition of integrals suffice.
    The measure of A and one distance integral are finite. *)
Lemma distance_subset_integral_bound (R : realType) (X : choiceType) (Y : metricType R)
    (phi : set X -> \bar R) (f : partial_function X Y) A (a b : R) (y z : Y) :
  is_measure phi -> is_measure_measurable_function phi f -> measure_measurable phi A ->
  phi A=b%:E -> is_measure_subset_integral phi A (partial_distance_to f y) a%:E ->
  exists c : R, is_measure_subset_integral phi A (partial_distance_to f z) c%:E /\
    (c<=a+mdist y z*b)%R.
Proof.
move=> hm hf hA hAb hy.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
pose d := mdist y z.
pose F := partial_function_zero_extension (0 : extended_real_line R) A (partial_distance_to f y).
pose G := partial_function_zero_extension (0 : extended_real_line R) A (partial_distance_to f z).
pose K := partial_function_total (fun x => (d%:E*(s x)%:E : extended_real_line R)).
have hK : is_measure_integral phi K (d*b)%R%:E.
  have h := @measure_nonnegative_extended_characteristic_integral R X phi hm A s d%:E
    hs hA ltac:(by rewrite lee_fin mdist_ge0).
  by rewrite hAb -EFinM in h.
have hsum : is_measure_integral phi (partial_extended_function_add F K) (a+d*b)%R%:E.
  apply: (@measure_integral_add R X phi hm F K a%:E (d*b)%R%:E _ hy hK).
  by rewrite /extended_add /=.
have hGm := @measurable_zero_extension R X (extended_real_line R) phi hm 0 A _ hA
  (@measurable_partial_distance_to R X Y phi f z hm hf).
have hGp := @zero_extension_nonnegative_almost R X phi hm A _
  (@partial_distance_to_nonnegative R X Y phi f z hm hf).
have [hGi hG0] := @nonnegative_measurable_function_integral R X phi hm G hGm hGp.
have horder : measure_almost_everywhere phi
    (partial_extended_le_locus G (partial_extended_function_add F K)).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measurable_function_domain hf))=> x [v hv].
  case: (pselect (A x))=> hx.
  - have hg : partial_function_graph G x (mdist v z)%:E.
      apply/partial_function_zero_extension_graph; left; split=> //; exists v; by split.
    have hF : partial_function_graph F x (mdist v y)%:E.
      apply/partial_function_zero_extension_graph; left; split=> //; exists v; by split.
    have hk : partial_function_graph K x d%:E.
      by rewrite /K /partial_function_total /= /s (characteristic_on_set hs hx) mule1.
    exists (mdist v z)%:E,(mdist v y+d)%R%:E; split=> //; split.
    + apply/partial_extended_function_add_graph; exists (mdist v y)%:E,d%:E.
      split=> //; split=> //; by rewrite /extended_add /=.
    + rewrite lee_fin; exact: metric_triangle.
  - have hg : partial_function_graph G x 0.
      apply/partial_function_zero_extension_graph; right; by split.
    have hF : partial_function_graph F x 0.
      apply/partial_function_zero_extension_graph; right; by split.
    have hk : partial_function_graph K x 0.
      by rewrite /K /partial_function_total /= /s (characteristic_off_set hs hx) mule0.
    exists 0,0; split=> //; split; last exact: lexx.
    apply/partial_extended_function_add_graph; exists 0,0; split=> //; split=> //.
    by rewrite /extended_add /= add0r.
have hbnd := @measure_integral_monotone R X phi hm G _ _ _ hGi hsum horder.
have hfin : measure_lower_integral phi G \is a fin_num.
  rewrite (ge0_fin_numE hG0); exact: le_lt_trans hbnd (ltry _).
exists (fine (measure_lower_integral phi G)); split.
- by rewrite fineK.
- by move: hbnd; rewrite -(fineK hfin) lee_fin.
Qed.
