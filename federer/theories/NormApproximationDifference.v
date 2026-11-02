(** Federer (1969), 3.1.2, p. 212: subtract two linear approximations
    and bound the difference by their two remainders. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [linear_difference_remainder_bound]: supporting passage
    from two approximate remainders to their linear difference in Federer
    3.1.2, p. 212. Each remainder receives half the error budget. *)
Lemma linear_difference_remainder_bound (R : realType) (X Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (L M : Hom X Y)
    (v : X) (q : Y) (e d : R) :
  NY (q-L v)<(e/2)*d -> NY (q-M v)<(e/2)*d ->
  NY ((L-M) v)<=e*d.
Proof.
move=> hL hM.
have hi : (L-M) v= -(q-L v)+(q-M v).
  change (L v-M v= -(q-L v)+(q-M v)).
  by rewrite opprB addrA subrK.
rewrite hi; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
rewrite (real_seminorm_negate hNY.1).
have hb := ltrD hL hM; nra.
Qed.

