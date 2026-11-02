(** Federer (1969), 2.4.8, p. 84: finite partial
    sums of a nonnegative family, evaluated using 2.1.1(1)–(3),
    p. 52. These graph identities support the passage from
    finite additivity of integrals to the countable sum. Source
    editions: PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP NonnegativeSum NumericalSum
  PartialNumericalSumUP PartialNumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_numerical_finite_sum]: supporting
    finite-sum evaluation for the partial sums in Federer
    2.4.8, p. 84, by 2.1.1(1)–(3), p. 52. *)
Lemma nonnegative_numerical_finite_sum (R : realType) (J : choiceType)
    (C : {fset J}) (u : J -> \bar R) :
  (forall j, j \in C -> 0 <= u j) ->
  numerical_sum [set j | j \in C] u = Some (\sum_(j <- C) u j).
Proof.
move=> hu; by rewrite (numerical_sum_nonnegative hu) (nonnegative_sum_finite hu).
Qed.

(** Source for [partial_numerical_finite_sum_graph]: finite
    graph form of the nonnegative pointwise sum in Federer
    2.4.8, p. 84, with exact common domain. *)
Lemma partial_numerical_finite_sum_graph (R : realType) (X : Type) (J : choiceType)
    (C : {fset J}) (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum [set j | j \in C] f g ->
  (forall j, j \in C -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  forall x z, partial_function_graph g x z <-> exists u : J -> \bar R,
    (forall j, j \in C -> partial_function_graph (f j) x (u j)) /\ (\sum_(j <- C) u j) = z.
Proof.
move=> hg hp x z; rewrite (hg x z); split.
- move=> [u [hu hs]]; exists u; split=> //.
  have hpos j : j \in C -> 0 <= u j by move=> hj; exact: hp j hj x (u j) (hu j hj).
  rewrite (nonnegative_numerical_finite_sum hpos) in hs; by case: hs.
- move=> [u [hu hs]]; exists u; split=> //.
  have hpos j : j \in C -> 0 <= u j by move=> hj; exact: hp j hj x (u j) (hu j hj).
  by rewrite (nonnegative_numerical_finite_sum hpos) hs.
Qed.
