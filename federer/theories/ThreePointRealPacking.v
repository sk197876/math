(** Federer (1969), 2.10.29, p. 194: scalar supporting estimate for at most
    two equal-length disjoint intervals meeting a short test interval. Three
    points separated by more than r cannot lie in an interval of length at
    most 2r. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [three_real_points_separated_short_interval]: supporting
    one-dimensional packing contradiction for
    2.10.29, p. 194. Expanding the three
    absolute-value comparisons handles every point
    order without a selected sorting implementation. *)
Lemma three_real_points_separated_short_interval (R : realType) (l u r x y z : R) :
  l<=x -> x<=u -> l<=y -> y<=u -> l<=z -> z<=u -> u-l<=2*r ->
  r<`|x-y| -> r<`|x-z| -> r<`|y-z| -> False.
Proof.
move=> hlx hxu hly hyu hlz hzu hlen.
rewrite !ltr_normr=> /orP[hxy|hxy] /orP[hxz|hxz] /orP[hyz|hyz]; lra.
Qed.
