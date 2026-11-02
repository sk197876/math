(** Federer (1969), 1.7.1, p. 28: the strict inequalities for two linearly
    independent vectors. These supporting facts use the existing
    finite-family definition of independence, with the two indices true and
    false. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Pair.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [independent_pair]: Federer 1.7.1, p. 28,
    the hypothesis that x and y are linearly independent. This is
    the existing finite-family predicate with a two-element index set. *)
Definition independent_pair (x y : V) :=
  finite_independent (fun b : bool => if b then x else y).

(** Source for [independent_pair_right_nonzero]: Federer
    1.7.1, p. 28, supporting fact: neither member of an independent
    pair vanishes. Here the second member is considered. *)
Lemma independent_pair_right_nonzero x y : independent_pair x y -> y != 0.
Proof.
move=> h; apply/eqP=> hy.
have hz : \sum_(b : bool) (if b then 0 else 1) *: (if b then x else y) = 0.
  by rewrite big_bool /= scale0r scale1r add0r hy.
have hh := h _ hz false.
by move: (oner_neq0 K); rewrite hh eqxx.
Qed.

(** Source for [independent_pair_left_nonzero]: Federer
    1.7.1, p. 28, the first member of an independent pair is nonzero. *)
Lemma independent_pair_left_nonzero x y : independent_pair x y -> x != 0.
Proof.
move=> h; apply/eqP=> hx.
have hz : \sum_(b : bool) (if b then 1 else 0) *: (if b then x else y) = 0.
  by rewrite big_bool /= scale0r scale1r addr0 hx.
have hh := h _ hz true.
by move: (oner_neq0 K); rewrite hh eqxx.
Qed.

(** Source for [independent_pair_not_scaled]: Federer
    1.7.1, p. 28, independent vectors cannot be scalar multiples.
    This excludes equality in the completed-square argument. *)
Lemma independent_pair_not_scaled x y :
  independent_pair x y -> forall a : K, x != a *: y.
Proof.
move=> h a; apply/eqP=> hx.
have hz : \sum_(b : bool) (if b then 1 else -a) *: (if b then x else y) = 0.
  by rewrite big_bool /= scale1r scaleNr hx addrN.
have hh := h _ hz true.
by move: (oner_neq0 K); rewrite hh eqxx.
Qed.
End Pair.
