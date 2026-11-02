(** Federer (1969), 2.1.1(5), p. 52: finiteness of a signed sum is
    equivalent to finiteness of its absolute sum. editions: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum
  NonnegativeSumSupport NonnegativeSumAdd NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_difference_finite]: Federer
    2.1.1(5), p. 52; supporting arithmetic: the difference of two
    nonnegative values is a finite real exactly when both are finite. *)
Lemma nonnegative_difference_finite (R : realType) (p n : \bar R) :
  0 <= p -> 0 <= n ->
  ((exists r : R, extended_subtract p n = Some r%:E) <-> (p < +oo) && (n < +oo)).
Proof.
case: p=> [p| |]; case: n=> [n| |] //= hp hn;
  rewrite /extended_subtract /extended_add /adde_def /= ?eqxx ?ltry ?ltxx /=.
- split=> // _; by exists (p - n)%R.
- by split=> [[r] //|].
- by split=> [[r] //|].
- by split=> [[r] //|].
Qed.

(** Source for [nonnegative_absolute_sum_parts]: Federer
    2.1.1(5), p. 52; supporting identity obtained from the pointwise
    absolute-parts identity and nonnegative additivity. *)
Lemma nonnegative_absolute_sum_parts (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  nonnegative_sum A (fun x => `|f x|) =
  nonnegative_sum A (fun x => extended_positive_part (f x)) +
  nonnegative_sum A (fun x => extended_negative_part (f x)).
Proof.
rewrite -nonnegative_sum_add; last 2 first.
- by move=> x _; exact: extended_positive_part_nonnegative.
- by move=> x _; exact: extended_negative_part_nonnegative.
apply: nonnegative_sum_ext=> x _; exact: extended_absolute_parts.
Qed.

(** Source for [numerical_sum_finite_iff_absolute]: Federer 2.1.1(5), p. 52,
    second equivalence; the signed sum is a real number exactly when its
    nonnegative absolute sum is finite. *)
Theorem numerical_sum_finite_iff_absolute (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (exists r : R, numerical_sum A f = Some r%:E) <->
  nonnegative_sum A (fun x => `|f x|) < +oo.
Proof.
rewrite /numerical_sum nonnegative_difference_finite ?nonnegative_sum_nonnegative //.
rewrite nonnegative_absolute_sum_parts.
pose p := nonnegative_sum A (fun x => extended_positive_part (f x)).
pose n := nonnegative_sum A (fun x => extended_negative_part (f x)).
have hp : 0 <= p := nonnegative_sum_nonnegative _ _.
have hn : 0 <= n := nonnegative_sum_nonnegative _ _.
change ((p < +oo) && (n < +oo) <-> p + n < +oo).
split=> [/andP[hpfin hnfin]|hs].
- exact: lte_add_pinfty.
- apply/andP; split.
  + exact: le_lt_trans (@leeDl R p n hn) hs.
  + exact: le_lt_trans (@leeDr R n p hp) hs.
Qed.
