(** Federer (1969), 2.4.13, p. 88: the weighted arithmetic-geometric mean
    inequality, with equality exactly when the two bases agree. The argument
    below proves strict concavity of log from its tangent inequality, then
    applies exp as in the book. No relevant entry occurs in Federer's
    erratum for this item. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialSealed RealExponentialLaws WeightedMeanAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Concavity.
Variable R : realType.
Local Notation L := (@RealExponential.logarithm R).

(** Source for [real_logarithm_weighted_concavity]: the logarithmic
    inequality in the proof of Federer 2.4.13, p. 88 The elementary strict
    concavity invoked there is derived from tangent bounds here. *)
Lemma real_logarithm_weighted_concavity (a b x y : R) :
  0 < a -> 0 < b -> a+b = 1 -> 0 < x -> 0 < y ->
  a*L x+b*L y <= L (a*x+b*y).
Proof.
move=> ha hb hab hx hy; pose w := a*x+b*y.
have hw : 0 < w := positive_weighted_mean ha hb hx hy.
have hxw : 0 < x/w by rewrite divr_gt0.
have hyw : 0 < y/w by rewrite divr_gt0.
have h1 := real_logarithm_tangent hxw.
have h2 := real_logarithm_tangent hyw.
have hsum := lerD (ler_wpM2l (ltW ha) h1) (ler_wpM2l (ltW hb) h2).
rewrite weighted_ratio_tangent_sum ?gt_eqF // in hsum.
rewrite !real_logarithm_ratio // weighted_difference_identity // in hsum.
by move: hsum; rewrite subr_le0.
Qed.

(** Source for [real_logarithm_weighted_strict_concavity]: strictness
    for different bases in Federer 2.4.13, p. 88;
    this supplies the printed equality condition. *)
Lemma real_logarithm_weighted_strict_concavity (a b x y : R) :
  0 < a -> 0 < b -> a+b = 1 -> 0 < x -> 0 < y -> x != y ->
  a*L x+b*L y < L (a*x+b*y).
Proof.
move=> ha hb hab hx hy hxy; pose w := a*x+b*y.
have hw : 0 < w := positive_weighted_mean ha hb hx hy.
have hxw : 0 < x/w by rewrite divr_gt0.
have hyw : 0 < y/w by rewrite divr_gt0.
have hne : x/w != 1.
  apply/negP=> /eqP /divr1_eq he.
  have hb0 : b != 0 by rewrite gt_eqF.
  have hne := weighted_mean_distinct_from_left hab hb0 hxy.
  apply: (negP hne); apply/eqP; exact he.
have h1 := real_logarithm_strict_tangent hxw hne.
have h2 := real_logarithm_tangent hyw.
have hleft : a*L (x/w) < a*(x/w-1) by rewrite ltr_pM2l.
have hsum := ltr_leD hleft (ler_wpM2l (ltW hb) h2).
rewrite weighted_ratio_tangent_sum ?gt_eqF // in hsum.
rewrite !real_logarithm_ratio // weighted_difference_identity // in hsum.
by move: hsum; rewrite subr_lt0.
Qed.
End Concavity.
