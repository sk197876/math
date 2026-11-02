(** Federer (1969), 2.6.3(3), p. 118: the section-measure function of A1
    times B is alpha(A1) times the characteristic function of B. A strictly
    positive factor cannot make a nonmeasurable B measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  CharacteristicFunctionUP MeasureUP MeasureSplit MeasurableFunctionUP CountableOrderIntervals
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureExtendedCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_characteristic_measurable_set]: supporting
    nonmeasurability test in Federer 2.6.3(3), p. 118,
    using the open positive ray. The positive weight may be infinite. *)
Lemma positive_characteristic_measurable_set (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (B : set X) (s : X -> R) (c : \bar R) :
  is_characteristic_function B s -> 0 < c ->
  is_measure_measurable_function mu (partial_function_total (fun x => c*(s x)%:E : extended_real_line R)) ->
  measure_measurable mu B.
Proof.
move=> hs hc hf.
have he : partial_function_preimage (partial_function_total (fun x => c*(s x)%:E : extended_real_line R))
    [set y | 0 < y] = B.
  apply/seteqP; split=> x.
  - move=> [z [<- hz]]; apply: contrapT=> hn.
    by rewrite /= (characteristic_off_set hs hn) mule0 ltxx in hz.
  - move=> hx; exists (c*(s x)%:E); split=> //.
    change (0 < c*(s x)%:E); by rewrite (characteristic_on_set hs hx) mule1.
rewrite -he; apply: (@measurable_function_open_preimage R X (extended_real_line R) mu _ hf).
exact: order_strict_upper_ray_open.
Qed.

(** Source for [nonnegative_extended_constant_integral]: supporting
    constant repeated-integral computation in Federer 2.6.3(3),
    p. 118. A nonnegative constant has integral c times
    the whole-space measure, including zero times infinity. *)
Lemma nonnegative_extended_constant_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : \bar R) :
  0 <= c -> is_measure_integral mu (partial_function_total (fun _ : X => (c : extended_real_line R))) (c*mu setT).
Proof.
move=> hc.
have hs : is_characteristic_function (@setT X) (fun _ => (1%R : R)).
  constructor=> x hx; first by [].
  by exfalso; apply: hx.
have hi := @measure_nonnegative_extended_characteristic_integral R X mu hm setT _ c hs (measure_measurable_whole hm) hc.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x y.
change (c*(1%R : R)%:E=y <-> c=y); by rewrite mule1.
Qed.
