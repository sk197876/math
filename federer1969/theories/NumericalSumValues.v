(** Federer (1969), 2.1.1(4)-(5), p. 52: the value and domain of a signed
    numerical sum. Supporting lemmas for the later identities. source
    editions: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum
  NonnegativeSumSupport NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_subtract_value]: Federer 2.1.1,
    p. 51; supporting identification of a defined partial difference
    with the scalar subtraction restricted to its valid domain. *)
Lemma extended_subtract_value (R : realType) (p n z : \bar R) :
  extended_subtract p n = Some z -> p - n = z.
Proof.
rewrite /extended_subtract /extended_add; case: (adde_def p (-n))=> //.
by move=> [].
Qed.

(** Source for [nonnegative_difference_value]: Federer
    2.1.1(5), p. 52; value of the difference when one variation
    is finite. *)
Lemma nonnegative_difference_value (R : realType) (p n : \bar R) :
  0 <= p -> 0 <= n -> (p < +oo) || (n < +oo) ->
  extended_subtract p n = Some (p-n).
Proof.
move=> hp hn hd; have [z hz] := (proj2 (nonnegative_difference_defined hp hn)) hd.
by rewrite (extended_subtract_value hz).
Qed.

(** Source for [numerical_sum_value]: Federer 2.1.1(4),
    p. 52; any defined sum equals the difference of its variations. *)
Lemma numerical_sum_value (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) z : numerical_sum A f = Some z ->
  nonnegative_sum A (fun x => extended_positive_part (f x)) -
  nonnegative_sum A (fun x => extended_negative_part (f x)) = z.
Proof. exact: extended_subtract_value. Qed.

(** Source for [numerical_sum_ext]: Federer 2.1.1(3)-(4),
    p. 52; equality of the summands on A preserves both domain and value. *)
Lemma numerical_sum_ext (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) :
  (forall x, A x -> f x = g x) -> numerical_sum A f = numerical_sum A g.
Proof.
move=> he; rewrite /numerical_sum.
have hp : nonnegative_sum A (fun x => extended_positive_part (f x)) =
    nonnegative_sum A (fun x => extended_positive_part (g x)).
  apply: nonnegative_sum_ext=> x hx; by rewrite (he x hx).
have hn : nonnegative_sum A (fun x => extended_negative_part (f x)) =
    nonnegative_sum A (fun x => extended_negative_part (g x)).
  apply: nonnegative_sum_ext=> x hx; by rewrite (he x hx).
by rewrite hp hn.
Qed.

(** Source for [numerical_sum_defined_subset]: Federer
    2.1.1(3)-(5), p. 52; supporting fact used in (9) and (13):
    restriction of a defined numerical sum remains defined. *)
Lemma numerical_sum_defined_subset (R : realType) (I : choiceType)
    (A B : set I) (f : I -> \bar R) z :
  B `<=` A -> numerical_sum A f = Some z -> exists w, numerical_sum B f = Some w.
Proof.
move=> hBA hz; apply/numerical_sum_defined; apply/orP.
have /numerical_sum_defined/orP[hp|hn] : exists w, numerical_sum A f = Some w by exists z.
- left; exact: le_lt_trans (nonnegative_sum_subset _ hBA) hp.
- right; exact: le_lt_trans (nonnegative_sum_subset _ hBA) hn.
Qed.
