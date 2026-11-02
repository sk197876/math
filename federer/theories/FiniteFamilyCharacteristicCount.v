(** Federer (1969), 3.2.39, p. 276: sums of
    actual characteristic functions count the finite containing family. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import RealMetricBackground CharacteristicFunctionUP FiniteFamilyMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_family_hit_count_indicator_sum]: supporting
    the cardinality in the first characteristic identity of
    Federer 3.2.39, p. 276. Each finite index contributes
    exactly one when its actual original set contains the point. *)
Lemma finite_family_hit_count_indicator_sum (X:Type) (I:finType) (K:I->set X) y:
  finite_family_hit_count K y=(\sum_(i:I) if asbool (K i y) then 1 else 0)%N.
Proof.
rewrite /finite_family_hit_count -sum1_card big_mkcond.
apply:eq_bigr=>i _; by rewrite inE.
Qed.

(** Source for [finite_family_characteristic_count]: the sum
    over C in G of t_C in Federer 3.2.39, p. 276.
    The characteristic functions are used only through their
    independent on/off laws; no implementation is exposed. *)
Lemma finite_family_characteristic_count (R:realType) (X:Type) (I:finType)
    (K:I->set X) (chi:I->X->real_line_metric R):
  (forall i,is_characteristic_function (K i) (chi i)) ->forall y,
    \sum_i chi i y=(finite_family_hit_count K y)%:R.
Proof.
move=>hChi y; rewrite finite_family_hit_count_indicator_sum natr_sum.
apply:eq_bigr=>i _; case:(asboolP (K i y))=>hi.
- by rewrite (characteristic_on_set (hChi i) hi).
- by rewrite (characteristic_off_set (hChi i) hi).
Qed.
