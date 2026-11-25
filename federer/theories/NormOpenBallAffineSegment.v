(** General normed-space geometry supporting Federer (1969),
    4.1.14, p. 370: sufficiently close approximating maps have
    their intervening segments in the same prescribed compact
    target neighbourhood. Reuse convexity of the earlier norm
    balls, 2.10.2(1), p. 171. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormConvexHullDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_open_ball_affine_segment]: the segment
    containment in the first construction paragraph of Federer
    4.1.14, p. 370. Both endpoints lie in the same open norm
    ball, so every intervening affine point does too. *)
Lemma norm_open_ball_affine_segment (R : realType) (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (z u v : Y) (r t : R) :
  NY (u-z)<r -> NY (v-z)<r -> 0<=t -> t<=1 ->
  NY ((1-t)*:u+t*:v-z)<r.
Proof.
move=> hu hv ht ht1.
pose b := Num.max (NY (u-z)) (NY (v-z)).
have hub : NY (u-z)<=b by rewrite /b le_max lexx orTb.
have hvb : NY (v-z)<=b by rewrite /b le_max lexx orbT.
have hConvex := @norm_ball_inner_convex R Y NY hNY z b
  u v hub hvb t ht ht1.
apply: le_lt_trans hConvex _.
by rewrite /b gt_max hu hv.
Qed.
