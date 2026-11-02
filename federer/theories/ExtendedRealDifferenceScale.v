(** Federer (1969), 2.1.1(6), p. 52: scaling a partial difference of
    nonnegative variations. editions: ExtendedRealPartial.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_difference_negate]: Federer
    2.1.1(6), p. 52, coefficient minus one; swapping nonnegative
    variations negates the difference and preserves undefinedness. *)
Lemma nonnegative_difference_negate (R : realType) (p n : \bar R) :
  0 <= p -> 0 <= n ->
  extended_subtract n p = omap -%E (extended_subtract p n).
Proof.
case: p=> [p| |]; case: n=> [n| |] //= hp hn;
  rewrite /extended_subtract /extended_add /adde_def /= ?eqxx //.
by rewrite opprB.
Qed.

(** Source for [nonnegative_difference_positive_scale]: Federer
    2.1.1(6), p. 52; a strictly positive real coefficient commutes
    with the partial difference, preserving its domain. *)
Lemma nonnegative_difference_positive_scale (R : realType) (p n : \bar R) (c : R) :
  (0 < c)%R -> 0 <= p -> 0 <= n ->
  extended_subtract (c%:E * p) (c%:E * n) =
    omap (fun x => c%:E * x) (extended_subtract p n).
Proof.
move=> hc.
have hcy : c%:E * (+oo : \bar R) = +oo by rewrite mulry gtr0_sg // mul1e.
have hcn : c%:E * (-oo : \bar R) = -oo by rewrite mulrNy gtr0_sg // mul1e.
case: p=> [p| |]; case: n=> [n| |] //= hp hn;
  rewrite ?hcy /extended_subtract /extended_add /adde_def /= ?eqxx ?hcy ?hcn //.
by rewrite -EFinM -!EFinD -EFinM mulrBr.
Qed.
