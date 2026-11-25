(** Federer (1969), 2.10.3, pp. 171–172: the exterior-product map is affine
    in each of its 2m variables, so its norm supremum is unchanged by
    replacing the source set by its convex hull. This supporting file proves
    preservation of convexity and norm bounds under a single affine map,
    using the affine-map laws recalled in 2.7.16, p. 133. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import AffineMaps InnerConvex ConvexHull RealNormUP NormConvexHullDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_preimage_inner_convex]: supporting
    separately affine argument for Federer 2.10.3, p. 172.
    The inverse image of a convex set under an affine
    map is convex. This intermediate fact is not printed
    as a separate numbered assertion. *)
Lemma affine_preimage_inner_convex (R : realType) (V W : lmodType R)
    (f : V -> W) (C : set W) :
  is_affine_map f -> is_inner_convex C -> is_inner_convex (f @^-1` C).
Proof.
move=> hf hC x y hx hy t ht ht1.
change (C (f ((1-t) *: x+t *: y))).
rewrite (hf x y (1-t) t ltac:(by rewrite subrK)).
exact: hC (f x) (f y) hx hy t ht ht1.
Qed.

(** Source for [affine_norm_sublevel_convex]: supporting
    norm-sublevel preimage for the separately affine proof
    in Federer 2.10.3, p. 172. Only the supplied
    norm laws are used; the target dimension is arbitrary. *)
Lemma affine_norm_sublevel_convex (R : realType) (V W : lmodType R)
    (f : V -> W) (N : W -> R) (hN : is_real_norm N) (b : R) :
  is_affine_map f -> is_inner_convex [set x | N (f x)<=b].
Proof.
move=> hf.
have hC : is_inner_convex [set w | N w<=b].
  have hh := @norm_ball_inner_convex R W N hN 0 b.
  have he : [set w | N (w-0)<=b]=[set w | N w<=b].
    by apply/seteqP; split=> w; rewrite /= subr0.
  by rewrite he in hh.
exact: affine_preimage_inner_convex hf hC.
Qed.

(** Source for [affine_norm_bound_convex_hull]: supporting
    one-variable extension of the norm bound in Federer
    2.10.3, p. 172. The hull is accessed only through
    its least-convex-superset law, without computing through
    its private existence construction. *)
Theorem affine_norm_bound_convex_hull (R : realType) (V W : lmodType R)
    (f : V -> W) (N : W -> R) (hN : is_real_norm N) (A : set V) (b : R) :
  is_affine_map f -> (forall x, A x -> N (f x)<=b) ->
  forall x, convex_hull A x -> N (f x)<=b.
Proof.
move=> hf hA x hx.
have hsub : A `<=` [set x | N (f x)<=b] by [].
exact (@convex_hull_least R V A _ hsub
  (@affine_norm_sublevel_convex R V W f N hN b hf) x hx).
Qed.
