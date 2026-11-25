(** Federer (1969), 2.6.4, pp. 118–119: rectangle characteristic functions
    with finite factor measures belong to the total-domain L1 tensor image.
    This supports the P0 and P1 density steps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureIntegralUP MeasureCharacteristicIntegral
  SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  CharacteristicUnionArithmetic SummableTensorImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_characteristic_summable]: supporting
    factor membership for the rectangular tensor in Federer
    2.6.4, p. 118, from 2.4.5, p. 83. *)
Lemma finite_characteristic_summable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s : X -> R) :
  is_characteristic_function A s -> measure_measurable mu A -> (mu A < +oo)%E ->
  summable_real_functions mu s.
Proof.
move=> hs hA hfin; have hf : mu A \is a fin_num.
  by rewrite ge0_fin_numE //; exact (@measure_nonnegative R X mu hm A).
exists (fine (mu A)); rewrite fineK //.
exact (@measure_characteristic_integral R X mu hm A s hs hA).
Qed.

(** Source for [finite_rectangle_characteristic_image]: the
    finite-factor rectangle case of the characteristic density
    assertion in Federer 2.6.4, pp. 118–119. The
    characteristic function belongs to the image exactly, including
    empty or null factors, without almost-everywhere identification. *)
Theorem finite_rectangle_characteristic_image (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y)
    (s : (X*Y) -> R) :
  measure_measurable alpha A -> (alpha A < +oo)%E ->
  measure_measurable beta B -> (beta B < +oo)%E ->
  is_characteristic_function (A `*` B) s -> separated_summable_image ha hb s.
Proof.
move=> hA hAf hB hBf hs.
pose a := @CharacteristicFunction.value R X A.
pose b := @CharacteristicFunction.value R Y B.
have ha' : is_characteristic_function A a := @CharacteristicFunction.laws R X A.
have hb' : is_characteristic_function B b := @CharacteristicFunction.laws R Y B.
have hprod := characteristic_rectangle_product ha' hb'.
have he : s=(fun p : X*Y => a p.1*b p.2).
  apply: funext=> p; exact (@characteristic_function_unique R (X*Y)%type (A `*` B) s
    (fun p => a p.1*b p.2) hs hprod p).
rewrite he; apply: separated_summable_image_product.
- exact (@finite_characteristic_summable R X alpha ha A a ha' hA hAf).
- exact (@finite_characteristic_summable R Y beta hb B b hb' hB hBf).
Qed.
