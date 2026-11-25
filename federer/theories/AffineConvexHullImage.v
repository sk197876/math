(** Federer (1969), 4.1.23, pp. 379–380:
    affine transfer preserves the whole hull of
    every polyhedral generator. The compact indices
    themselves need not be convex. Reuse the
    original least-convex-superset laws of 2.10.2. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import AffineMaps InnerConvex ConvexHull
  AffineConvexPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_image_inner_convex]: affine
    images preserve convexity, supporting the rotations
    and generator-hull transfer in Federer 4.1.23,
    pp. 379–380, by 2.7.16, p. 133. *)
Lemma affine_image_inner_convex (R : realType) (X Y : lmodType R)
    (f : X -> Y) (A : set X) :
  is_affine_map f -> is_inner_convex A -> is_inner_convex (f @` A).
Proof.
move=> hAffine hConvex x y [a ha <-] [b hb <-] t ht ht1.
exists ((1-t)*:a+t*:b); first exact: hConvex a b ha hb t ht ht1.
exact: hAffine a b (1-t) t ltac:(by rewrite subrK).
Qed.

(** Source for [affine_convex_hull_image]: the
    full vertex hull is transported exactly by
    every affine map in Federer 4.1.23,
    pp. 379–380. No injectivity, convexity of
    a containing compact set, or nonempty generator
    set is imposed. *)
Theorem affine_convex_hull_image (R : realType) (X Y : lmodType R)
    (f : X -> Y) (A : set X) (hAffine : is_affine_map f) :
  f @` convex_hull A=convex_hull (f @` A).
Proof.
apply/seteqP; split.
- move=> y [x hx <-].
  have hContains : A `<=` f @^-1` convex_hull (f @` A).
    move=> a ha; apply: convex_hull_includes; by exists a.
  exact: (@convex_hull_least R X A _ hContains
    (@affine_preimage_inner_convex R X Y f _ hAffine
      (@convex_hull_convex R Y (f @` A))) x hx).
- apply: convex_hull_least.
  + move=> y [x hx <-]; exists x; first exact: convex_hull_includes hx.
    reflexivity.
  + exact: (@affine_image_inner_convex R X Y f (convex_hull A)
      hAffine (@convex_hull_convex R X A)).
Qed.
