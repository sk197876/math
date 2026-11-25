(** Federer (1969), 2.1.1, pp. 52-53: numerical sums over arbitrary sets.
    Finite sets and extended-real scalar arithmetic are background; the
    arbitrary summation operator and its laws are developed here. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_nonnegative_sum]: Federer 2.1.1(3), p. 52; specification
    by finite subsums: the value bounds every finite subsum and is below
    every such bound. The laws are meaningful for arbitrary f; the intended
    summation domain is nonnegative f. *)
Record is_nonnegative_sum (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) c : Prop := {
  nonnegative_sum_finite_upper : forall (B : {fset I}),
    (forall x, x \in B -> A x) -> (\sum_(x <- B) f x) <= c;
  nonnegative_sum_finite_least : forall d,
    (forall (B : {fset I}), (forall x, x \in B -> A x) ->
      (\sum_(x <- B) f x) <= d) -> c <= d
}.

(** Source for [nonnegative_sum_unique]: Federer 2.1.1(3), p. 52, supporting
    uniqueness of the finite-subsum specification *)
Lemma nonnegative_sum_unique (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) c d :
  is_nonnegative_sum A f c -> is_nonnegative_sum A f d -> c = d.
Proof.
move=> hc hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (nonnegative_sum_finite_least hc (nonnegative_sum_finite_upper hd)).
- exact: (nonnegative_sum_finite_least hd (nonnegative_sum_finite_upper hc)).
Qed.
