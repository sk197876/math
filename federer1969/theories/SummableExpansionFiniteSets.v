(** Federer (1969), 2.5.10, p. 101: the nonnegative summable integrands can
    be expanded into characteristic functions of finite-measure sets. This
    follows from the positive weights of 2.3.3, p. 76, and the integral
    identity of 2.4.8, p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  NonnegativeSum WeightedCharacteristicExpansionUP WeightedCharacteristicIntegral
  MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_expansion_sets_finite]: supporting
    finite-support consequence for the characteristic
    expansion in Federer 2.5.10, p. 101.
    Every positive coefficient forces the corresponding
    measurable set to have finite measure when the
    integral of the expansion is finite. *)
Lemma summable_expansion_sets_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (r : nat -> R)
    (E : nat -> set X) (s : nat -> X -> R) (a : R) :
  (forall n, (0<r n)%R) -> is_weighted_characteristic_expansion mu f r E s ->
  is_measure_integral mu (partial_function_total f) a%:E -> forall n, mu (E n) < +oo.
Proof.
move=> hr he hi n.
have hsum := @weighted_characteristic_expansion_integral R X mu hm f r E s hr he.
have ht := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
  (fun j => (r j)%:E*mu (E j)) n I.
rewrite (measure_integral_unique hsum hi) in ht.
have hlt := le_lt_trans ht (ltry a).
case hz: (mu (E n))=> [b| |]; first exact: ltry.
- have hp : (0 : \bar R)<(r n)%:E by rewrite lte_fin; exact: hr.
  by move: hlt; rewrite hz (gt0_muley hp) ltxx.
- by rewrite ltNye.
Qed.
