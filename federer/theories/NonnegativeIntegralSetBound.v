(** Supporting the arbitrary-set product argument in Federer (1969),
    2.10.46, p. 204: if a nonnegative integrable function is at least c on
    A, its integral bounds c times the outer measure of A. The set A need
    not be measurable. This follows from the characteristic upper bound of
    2.4.5, p. 84, and upper-integral comparison and scaling in 2.4.3(2),(5),
    pp. 81–82. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic MeasureStepIntegralIdentification
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureCharacteristicUpperBound
  MeasureUpperIntegralMonotone MeasureUpperIntegralScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_integral_arbitrary_set_bound]:
    supporting outer-measure comparison for 2.10.46, p. 204,
    derived from 2.4.5 and 2.4.3 without assuming
    measurability of the compared set. *)
Theorem nonnegative_integral_arbitrary_set_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (A : set X) (c : R) (a : \bar R) :
  (forall x, 0<=f x) -> (0<c)%R -> (forall x, A x -> c%:E<=f x) ->
  is_measure_integral mu (partial_function_total f) a -> c%:E*mu A<=a.
Proof.
move=> hf hc hA hi.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
pose g := partial_real_function_embed (partial_function_total s).
have hchar := @measure_characteristic_upper_bound R X mu hm A s hs.
have hC : 0<=c%:E by rewrite lee_fin; exact: ltW hc.
have he : measure_upper_integral mu (partial_function_total f)=a.
  exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
rewrite -he; apply: le_trans (lee_wpmul2l hC hchar) _.
rewrite -(@measure_upper_integral_positive_scale R X mu hm c g hc).
apply: (@measure_upper_integral_monotone R X mu hm).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (c%:E*(s x)%:E),(f x); split.
- exists (s x)%:E; split=> //; exists (s x); by split.
- split=> //; case: (pselect (A x))=> hx.
  + rewrite /s (characteristic_on_set hs hx) mule1; exact: hA.
  + rewrite /s (characteristic_off_set hs hx) mule0; exact: hf.
Qed.
