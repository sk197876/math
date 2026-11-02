(** Federer (1969), 3.1.24, pp. 239–240: the
    triangle inequality applies to the filtered sum of inverse
    composition terms, in the project's abstract norm interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_seminorm_filtered_sum]: supporting the
    norm bound on the sum over T(p) in Federer 3.1.24,
    pp. 239–240. A finite filtered sum has seminorm
    at most the corresponding sum of seminorms. Inactive
    terms contribute zero by the proved seminorm laws. *)
Lemma real_seminorm_filtered_sum (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_seminorm NY) (I:finType) (P:pred I) (f:I->Y) :
  NY (\sum_(i|P i) f i)<=\sum_(i|P i) NY (f i).
Proof.
rewrite !big_mkcond.
apply:le_trans (real_seminorm_sum hNY _) _.
have he:(\sum_(i|P i) NY (f i))=\sum_i (if P i then NY (f i) else 0).
  by rewrite big_mkcond.
rewrite he.
apply:ler_sum=>i _; case:(P i); first exact:le_refl.
by rewrite (real_seminorm_zero hNY).
Qed.
