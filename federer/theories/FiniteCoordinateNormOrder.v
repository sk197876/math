(** Federer (1969), 3.2.27, p. 263: supporting
    order of Euclidean norms of nonnegative coordinate
    masses in the arbitrary-source lower comparison.
    The sum-of-squares formula is 1.7.5, p. 32. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_nonnegative_coordinate_norm_mono]:
    supporting coordinatewise lower-bound reduction in
    3.2.27, pp. 262–263. Squaring is monotone
    on nonnegative coordinates and the nonnegative
    square root is monotone on their sums. *)
Lemma finite_nonnegative_coordinate_norm_mono (R:realType) (I:finType) (a b:I->R):
  (forall i,0<=a i<=b i) ->
  Num.sqrt (\sum_i (a i)^+2)<=Num.sqrt (\sum_i (b i)^+2).
Proof.
move=>hAB; apply:ler_wsqrtr; apply:ler_sum=>i _.
have /andP[ha hab]:=hAB i.
by rewrite (ler_sqr ha (le_trans ha hab)).
Qed.
