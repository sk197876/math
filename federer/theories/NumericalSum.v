(** Federer (1969), 2.1.1(4)-(5), pp. 52-53: signed numerical summation and
    its domain. Undefined sums are represented by None; in particular, two
    infinite variations cannot be subtracted. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum]: Federer 2.1.1(4), p. 52;
    the signed sum is the partial difference of the sums of the
    positive and negative parts. *)
Definition numerical_sum (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :=
  extended_subtract
    (nonnegative_sum A (fun x => extended_positive_part (f x)))
    (nonnegative_sum A (fun x => extended_negative_part (f x))).

(** Source for [nonnegative_difference_defined]: Federer
    2.1.1(5), p. 52, supporting arithmetic criterion: a difference
    of nonnegative extended reals is defined unless both are infinite. *)
Lemma nonnegative_difference_defined (R : realType) (p n : \bar R) :
  0 <= p -> 0 <= n ->
  ((exists z, extended_subtract p n = Some z) <-> (p < +oo) || (n < +oo)).
Proof.
move=> hp hn; rewrite /extended_subtract extended_add_defined.
case: p hp=> [p| |] hp; case: n hn=> [n| |] hn //;
  by rewrite /adde_def /= ?eqxx ?ltry.
Qed.

(** Source for [numerical_sum_defined]: Federer 2.1.1(5), p. 52, first
    equivalence; the sum is defined exactly when one of the two variations
    is finite. *)
Theorem numerical_sum_defined (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (exists z, numerical_sum A f = Some z) <->
  (nonnegative_sum A (fun x => extended_positive_part (f x)) < +oo) ||
  (nonnegative_sum A (fun x => extended_negative_part (f x)) < +oo).
Proof.
apply: nonnegative_difference_defined; exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [numerical_sum_nonnegative]: Federer 2.1.1(3)-(4), p. 52;
    extending summation by positive and negative parts preserves every
    nonnegative sum. *)
Theorem numerical_sum_nonnegative (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (forall x, A x -> 0 <= f x) -> numerical_sum A f = Some (nonnegative_sum A f).
Proof.
move=> hf; rewrite /numerical_sum.
have hp : nonnegative_sum A (fun x => extended_positive_part (f x)) = nonnegative_sum A f.
  apply: nonnegative_sum_ext=> x hx; rewrite /extended_positive_part.
  exact: max_l (hf x hx).
have hn : nonnegative_sum A (fun x => extended_negative_part (f x)) = 0.
  apply: nonnegative_sum_zero=> x hx.
  rewrite /extended_negative_part /extended_positive_part max_r // oppe_le0.
  exact: hf.
by rewrite hp hn /extended_subtract oppe0 /extended_add fin_num_adde_defl // adde0.
Qed.

(** Source for [numerical_sum_empty]: Federer 2.1.1, p. 52,
    sentence before (1), extended to signed functions by (4). *)
Lemma numerical_sum_empty (R : realType) (I : choiceType) (f : I -> \bar R) :
  numerical_sum set0 f = Some 0.
Proof.
rewrite numerical_sum_nonnegative; first by rewrite nonnegative_sum_empty.
by move=> x [].
Qed.
