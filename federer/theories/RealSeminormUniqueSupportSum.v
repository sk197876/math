(** Federer (1969), 4.1.12, p. 369: at
    each point at most one separated
    cutoff contributes. Combine the original
    triangle inequality with the proved scalar
    unique-support sum bound of 1.7.5, p. 33. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP FiniteSparseSumBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_seminorm_unique_support_sum_bound]:
    a finite vector sum with at most
    one active term retains the common
    seminorm bound C, supporting both
    printed psi_m estimates in Federer
    4.1.12, p. 369. Empty
    families and zero bounds are retained. *)
Lemma real_seminorm_unique_support_sum_bound (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_seminorm NY) (I:finType) (P:pred I) (f:I->Y) C:
  0<=C->(forall i,NY (f i)<=C)->(forall i,~~P i->f i=0)->
  (forall i j,P i->P j->i=j)->NY (\sum_i f i)<=C.
Proof.
move=>hC hBound hOff hUnique.
have hCompare:(\sum_i NY (f i))<=\sum_i (if P i then C else 0).
  apply:ler_sum=>i _;case:ifP=>hi;first exact:hBound i.
  have hNot:~~P i by rewrite hi.
  by rewrite (hOff i hNot) (real_seminorm_zero hNY).
apply:le_trans (real_seminorm_sum hNY f) _.
apply:le_trans hCompare _.
rewrite -big_mkcond;exact:unique_support_sum_bound hC hUnique.
Qed.
