(** Federer (1969), 2.1.1(13), p. 53: convergence under increasing
    exhaustion, for every defined numerical sum. Source context:
    NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderLimit
  ExtendedRealDifferenceLimit NonnegativeSum NonnegativeSumContinuity
  NumericalSum NumericalSumValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_increasing_exhaustion]: Federer
    2.1.1(13), p. 53; all restricted sums are defined and their
    values converge in the extended order topology to the original
    sum. The limit may be either infinity. *)
Theorem numerical_sum_increasing_exhaustion (R : realType) (I : choiceType)
    (A : set I) (B : nat -> set I) (f : I -> \bar R) z :
  (forall n m, (n <= m)%N -> B n `<=` B m) ->
  (forall n, B n `<=` A) ->
  (forall x, A x -> exists n, B n x) ->
  numerical_sum A f = Some z ->
  exists s : nat -> \bar R,
    (forall n, numerical_sum (B n) f = Some (s n)) /\ extended_order_limit s z.
Proof.
move=> hm hsub hcover hz.
pose fp x := extended_positive_part (f x).
pose fn x := extended_negative_part (f x).
pose p n := nonnegative_sum (B n) fp.
pose q n := nonnegative_sum (B n) fn.
pose P := nonnegative_sum A fp.
pose N := nonnegative_sum A fn.
have hp n : p n <= P by apply: nonnegative_sum_subset; exact: hsub.
have hn n : q n <= N by apply: nonnegative_sum_subset; exact: hsub.
have ht : (P < +oo) || (N < +oo).
  apply/numerical_sum_defined; by exists z.
have hpl := nonnegative_sum_increasing_limit fp hm hsub hcover.
have hnl := nonnegative_sum_increasing_limit fn hm hsub hcover.
exists (fun n => p n-q n); split.
- move=> n; change (extended_subtract (p n) (q n) = Some (p n-q n)).
  apply: nonnegative_difference_value; try exact: nonnegative_sum_nonnegative.
  apply/orP; move/orP: ht=> [h|h].
  + left; exact: le_lt_trans (hp n) h.
  + right; exact: le_lt_trans (hn n) h.
- rewrite -(numerical_sum_value hz).
  apply: extended_nonnegative_difference_limit ht hp hn hpl.2 hnl.2;
    exact: nonnegative_sum_nonnegative.
Qed.
