(** Supporting endpoint estimate for Federer (1969), 2.6.3(2), pp. 117–118:
    the first primitive tends to zero as its upper endpoint tends to
    infinity. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RationalFubiniKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rational_first_primitive_bound]: supporting bound
    |(a^2-a*y)/(a+y)^3| <= 1/a for positive a,y, justifying the zero limit
    in Federer 2.6.3(2), p. 118 The bound is proved algebraically. *)
Lemma rational_first_primitive_bound (R : realType) (y a : R) :
  0 < y -> 0 < a -> `|rational_first_primitive y a| <= a^-1.
Proof.
move=> hy ha; have ha0 := ltW ha; have hy0 := ltW hy.
have hp : 0 < a+y by rewrite addr_gt0.
have hp0 := ltW hp.
have hnum : `|a^+2-a*y| <= a^+2+a*y.
  apply: le_trans (ler_normB _ _) _.
  by rewrite (ger0_norm (exprn_ge0 2 ha0)) (ger0_norm (mulr_ge0 ha0 hy0)).
have hi0 : 0 <= ((a+y)^+3)^-1 by rewrite invr_ge0 exprn_ge0.
have h1 := ler_wpM2r hi0 hnum.
rewrite /rational_first_primitive normrM normfV (ger0_norm (exprn_ge0 3 hp0)).
apply: le_trans h1 _.
have he : (a^+2+a*y)/((a+y)^+3) = a/((a+y)^+2).
  by field; rewrite (gt_eqF hp).
rewrite he.
have h2 : a/((a+y)^+2) <= (a+y)^-1.
  rewrite (ler_pdivrMr _ _ (exprn_gt0 2 hp)).
  have he2 : (a+y)^-1*(a+y)^+2=a+y by field; rewrite (gt_eqF hp).
  rewrite he2; lra.
apply: le_trans h2 _.
by rewrite lef_pV2 ?inE //; lra.
Qed.
