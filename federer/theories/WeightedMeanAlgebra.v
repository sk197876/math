(** Federer (1969), 2.4.13, p. 88: the weighted arithmetic-geometric mean
    inequality, with equality exactly when the two bases agree. The argument
    below proves strict concavity of log from its tangent inequality, then
    applies exp as in the book. No relevant entry occurs in Federer's
    erratum for this item. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_difference_identity]: supporting scalar
    algebra for the strict-concavity proof in Federer 2.4.13,
    p. 88. This identity is not separately asserted in the book. *)
Lemma weighted_difference_identity (R : realType) (a b x y z : R) :
  a+b = 1 -> a*(x-z)+b*(y-z) = a*x+b*y-z.
Proof. by move=> hab; rewrite !mulrBr addrACA -opprD -mulrDl hab mul1r. Qed.

(** Source for [weighted_ratio_tangent_sum]: supporting cancellation
    of the weighted tangent terms at the arithmetic mean in
    Federer 2.4.13, p. 88. *)
Lemma weighted_ratio_tangent_sum (R : realType) (a b x y : R) :
  a+b = 1 -> a*x+b*y != 0 ->
  a*(x/(a*x+b*y)-1)+b*(y/(a*x+b*y)-1) = 0.
Proof.
move=> hab hw; by rewrite weighted_difference_identity // !mulrA -mulrDl mulfV // subrr.
Qed.

(** Source for [positive_weighted_mean]: positivity of the
    arithmetic mean needed to apply log in Federer 2.4.13,
    p. 88. *)
Lemma positive_weighted_mean (R : realType) (a b x y : R) :
  0 < a -> 0 < b -> 0 < x -> 0 < y -> 0 < a*x+b*y.
Proof. by move=> ha hb hx hy; apply: addr_gt0; exact: mulr_gt0. Qed.

(** Source for [weighted_mean_distinct_from_left]: supporting
    equality analysis in Federer 2.4.13, p. 88:
    a strict convex combination of distinct bases differs from
    the first base. Only the second weight must be nonzero here. *)
Lemma weighted_mean_distinct_from_left (R : realType) (a b x y : R) :
  a+b = 1 -> b != 0 -> x != y -> x != a*x+b*y.
Proof.
move=> hab hb hxy; apply/negP=> /eqP he.
have h : a*x+b*x = a*x+b*y by rewrite -mulrDl hab mul1r -he.
have h' : b*x=b*y := addrI (a*x) h.
have hexy : x=y := mulfI hb h'.
by move: hxy; rewrite hexy eqxx.
Qed.
