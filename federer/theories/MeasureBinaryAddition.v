(** Supporting addition of the two continuous-part measures in Federer
    (1969), 2.9.20, pp. 165–166. The measure and measurability laws follow
    directly from 2.1.1(2), p. 52, and 2.1.2, pp. 53–54. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_binary_addition_is_measure]: supporting measure sum
    in Federer 2.9.20, p. 166 Add the countable-cover inequalities and
    commute the two nonnegative sums, including possible positive infinity. *)
Lemma measure_binary_addition_is_measure (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) : is_measure mu -> is_measure nu ->
  is_measure (fun A => mu A+nu A).
Proof.
move=> hm hn; constructor.
- move=> A; exact: adde_ge0 (measure_nonnegative hm A) (measure_nonnegative hn A).
- move=> A F hF hcover.
  rewrite (@nonnegative_sum_add R [the choiceType of set X] F mu nu
    (fun B _ => measure_nonnegative hm B) (fun B _ => measure_nonnegative hn B)).
  exact: leeD (@measure_countable_cover R X mu hm A F hF hcover)
    (@measure_countable_cover R X nu hn A F hF hcover).
Qed.

(** Source for [measure_binary_addition_measurable]: supporting finite
    additivity for the sum measure in Federer 2.9.20, p. 166 A set
    measurable for both component measures is measurable for their sum. *)
Lemma measure_binary_addition_measurable (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (A : set X) :
  measure_measurable mu A -> measure_measurable nu A ->
  measure_measurable (fun B => mu B+nu B) A.
Proof. by move=> hA hA' T; rewrite (hA T) (hA' T) addeACA. Qed.
