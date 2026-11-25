(** Federer (1969), 2.1.1(12), p. 53: a real-valued numerical sum has
    countable support. Source context: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumCountable NumericalSum NumericalSumAbsolute.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_countable_support]: Federer
    2.1.1(12), p. 53; finite real total implies countable nonzero
    support, without imposing countability on the original index set. *)
Theorem numerical_sum_countable_support (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (exists r : R, numerical_sum A f = Some r%:E) ->
  countable (A `&` [set x | f x != 0]).
Proof.
move=> /numerical_sum_finite_iff_absolute hs.
have ha : forall x, A x -> 0 <= `|f x| by move=> x _; exact: abse_ge0.
have hc := nonnegative_sum_countable_support ha hs.
have he : (A `&` [set x | `|f x| != 0]) = (A `&` [set x | f x != 0]).
  by apply/seteqP; split=> x [hx hn]; split=> //; move: hn; rewrite /= abse_eq0.
by rewrite he in hc.
Qed.
