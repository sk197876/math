(** Archimedean background for Federer (1969), Chapter 2: a positive real
    number exceeds the reciprocal of some positive integer. This scalar fact
    supports the level arguments of 2.5.11, p. 102, and the coordinate
    argument of 2.5.15, pp. 108-109. The real field is an Archimedean
    ordered field as in Federer 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_reciprocal_below]: supporting Archimedean fact
    for Federer 2.5.11, p. 102, and 2.5.15, p. 109: for positive x
    there is a positive integer n with 1/n < x. *)
Lemma real_reciprocal_below (R : realType) (x : R) :
  0 < x -> exists n : nat, n.+1%:R^-1 < x.
Proof.
move=> hx; have hxi : 0 < x^-1 by rewrite invr_gt0.
exists (Num.bound x^-1).
rewrite -[x in (_ < x)]invrK ltf_pV2 ?posrE ?ltr0n //.
apply: lt_le_trans (archi_boundP (ltW hxi)) _.
by rewrite ler_nat.
Qed.
