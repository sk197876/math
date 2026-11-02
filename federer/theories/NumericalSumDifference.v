(** Federer (1969), 2.1.1(4),(7), pp. 52-53: subtracting two nonnegative
    sums when their difference is defined. This supports the signed
    additivity and regrouping proofs. editions: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial ExtendedRealBalance
  ExtendedRealDifferenceParts NonnegativeSum NonnegativeSumSupport
  NonnegativeSumAdd NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_difference_domain]: Federer 2.1.1(7), p. 53;
    supporting pointwise domain fact. If one total variation is finite, the
    two terms at each point cannot both be positive infinity. *)
Lemma nonnegative_sum_difference_domain (R : realType) (I : choiceType)
    (A : set I) (u v : I -> \bar R) :
  (forall x, A x -> 0 <= u x) -> (forall x, A x -> 0 <= v x) ->
  (nonnegative_sum A u < +oo) || (nonnegative_sum A v < +oo) ->
  forall x, A x -> adde_def (u x) (-v x).
Proof.
move=> hu hv htot x hx.
have ht : (u x < +oo) || (v x < +oo).
  apply/orP; move/orP: htot=> [h|h].
  - left; exact: le_lt_trans (nonnegative_sum_term u hx) h.
  - right; exact: le_lt_trans (nonnegative_sum_term v hx) h.
have he := (proj2 (nonnegative_difference_defined (hu x hx) (hv x hx))) ht.
exact: (proj1 (extended_add_defined (u x) (-v x))) he.
Qed.

(** Source for [numerical_sum_difference]: Federer 2.1.1(7),
    p. 53, supporting subtraction of nonnegative summands.
    If the difference of the two totals is defined, then summing
    the pointwise differences yields exactly that partial difference. *)
Theorem numerical_sum_difference (R : realType) (I : choiceType)
    (A : set I) (u v : I -> \bar R) :
  (forall x, A x -> 0 <= u x) -> (forall x, A x -> 0 <= v x) ->
  (nonnegative_sum A u < +oo) || (nonnegative_sum A v < +oo) ->
  numerical_sum A (fun x => u x-v x) =
    extended_subtract (nonnegative_sum A u) (nonnegative_sum A v).
Proof.
move=> hu hv ht; have hd := nonnegative_sum_difference_domain hu hv ht.
rewrite /numerical_sum; apply: nonnegative_difference_balance.
- exact: nonnegative_sum_nonnegative.
- exact: nonnegative_sum_nonnegative.
- exact: nonnegative_sum_nonnegative.
- exact: nonnegative_sum_nonnegative.
- apply: nonnegative_sum_mono=> x hx; exact: nonnegative_difference_positive_bound (hu x hx) (hv x hx).
- apply: nonnegative_sum_mono=> x hx; exact: nonnegative_difference_negative_bound (hu x hx) (hv x hx) (hd x hx).
- rewrite -!nonnegative_sum_add.
  + apply: nonnegative_sum_ext=> x hx; exact: nonnegative_difference_parts_balance (hu x hx) (hv x hx) (hd x hx).
  + by move=> x _; exact: extended_negative_part_nonnegative.
  + exact hu.
  + by move=> x _; exact: extended_positive_part_nonnegative.
  + exact hv.
- exact ht.
Qed.
