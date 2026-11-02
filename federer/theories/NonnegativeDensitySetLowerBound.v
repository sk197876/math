(** Federer (1969), 3.2.7, p. 246: supporting
    lower bounds for the weighted multiplicity density.
    The underlying laws are 2.4.3(2),(5), pp. 81–82,
    2.4.5, p. 84, and 2.4.10, p. 85.
    Neither density nor comparison set is assumed measurable. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialZeroExtension PartialExtendedOrderLoci MeasureStepIntegralIdentification MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensityUP
  MeasureSubsetIntegral MeasureIntegralUP MeasureIntegralBounds MeasureCharacteristicUpperBound
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUpperIntegralScale MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_density_set_lower_bound]:
    comparison estimate supporting the infinite weighted
    multiplicity in Federer 3.2.7, p. 246.
    If h is nonnegative and at least c on A,
    its upper-integral density measure gives A mass
    at least c times its original outer measure. *)
Lemma nonnegative_density_set_lower_bound (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (h:X->extended_real_line R) (A:set X) (c:R):
  is_measure_density mu (partial_function_total h) nu ->
  (forall x,0<=h x) -> (0<c)%R ->
  (forall x,A x -> c%:E<=h x) -> c%:E*mu A<=nu A.
Proof.
move=>hn hp hc hA.
pose s:=@CharacteristicFunction.value R X A.
have hs:=@CharacteristicFunction.laws R X A.
pose g:=partial_real_function_embed (partial_function_total s).
have hChar:=@measure_characteristic_upper_bound R X mu hm A s hs.
have hC:0<=c%:E by rewrite lee_fin; exact:ltW hc.
rewrite (hn A) /measure_subset_upper_integral.
apply:le_trans (lee_wpmul2l hC hChar) _.
rewrite -(@measure_upper_integral_positive_scale R X mu hm c g hc).
apply:(@measure_upper_integral_monotone R X mu hm).
apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
case:(pselect (A x))=>hx.
- exists (c%:E*(s x)%:E),(h x); split.
  + exists (s x)%:E; split=>//; exists (s x); by split.
  + split.
    * apply/partial_function_zero_extension_graph; left; by split.
    * rewrite /s (characteristic_on_set hs hx) mule1; exact:hA.
- exists (c%:E*(s x)%:E),0; split.
  + exists (s x)%:E; split=>//; exists (s x); by split.
  + split.
    * apply/partial_function_zero_extension_graph; right; by split.
    * by rewrite /s (characteristic_off_set hs hx) mule0.
Qed.
