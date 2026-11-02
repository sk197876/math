(** Supporting the two numerical jump sums in Federer (1969), 2.10.14, p.
    177, with the nonnegative numerical sums of 2.1.1, pp. 52–53. Specify a
    measure by the finite-sum supremum laws for its prescribed singleton
    weights. The implementation remains behind an opaque module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_weighted_counting_measure]: supporting universal
    specification of the atomic jump budgets in 2.10.14, p. 177.
    On each set the value obeys precisely the finite-subsum
    supremum laws of 2.1.1, pp. 52–53. Measure laws are
    proved consequences when the prescribed weights are nonnegative. *)
Definition is_weighted_counting_measure (R : realType) (X : choiceType)
    (w : X -> \bar R) (mu : set X -> \bar R) :=
  forall A, is_nonnegative_sum A w (mu A).
