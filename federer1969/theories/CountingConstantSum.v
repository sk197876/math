(** Constant nonnegative sums and counting measure, from Federer (1969),
    2.1.1(6), p. 52, and 2.1.2, p. 54. This adapter supports cylinder costs
    in the local counterexample for 2.3.8, p. 78. Source context:
    CountingFinitePredicate.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import CountingMeasure NonnegativeSum NonnegativeSumSupport NonnegativeSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_constant_sum_counting]: a finite
    nonnegative constant times counting measure equals the constant
    sum; direct combination of Federer 2.1.1(6), p. 52,
    and 2.1.2, p. 54, supporting 2.3.8. *)
Lemma nonnegative_constant_sum_counting (R : realType) (I : choiceType)
    (A : set I) (c : R) : (0 <= c)%R ->
  nonnegative_sum A (fun _ => c%:E) = c%:E * @counting_measure R I A.
Proof.
move=> hc; rewrite counting_measure_sum -nonnegative_sum_scale //.
apply: nonnegative_sum_ext=> x _; by rewrite mule1.
Qed.
