(** Federer (1969), 3.2.35, p. 271:
    the radial gauge of a convex open body
    is Lipschitz, supporting the rectifiability of
    its corrected radial boundary parametrization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealNormUP InnerConvex MinkowskiGaugeUP MinkowskiGaugeConvex
  NormMinkowskiGaugeBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_minkowski_gauge_lipschitz]:
    the gauge regularity needed for the
    n-1 rectifiable boundary in Federer 3.2.35,
    p. 271. Convexity gives subadditivity;
    the original inner ball gives the norm
    bound in each direction. This proves a
    global pairwise bound from the independent
    infimum laws and original set membership. *)
Lemma norm_minkowski_gauge_lipschitz (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) g r:
  is_minkowski_gauge S g ->is_inner_convex S ->0<r ->
  (forall y:V,N y<r ->S y) ->
  forall x y:V,`|g x-g y|<=N (x-y)/r.
Proof.
move=>hG hConvex hr hBall x y.
rewrite ler_norml; apply/andP; split.
- have hTri:=minkowski_gauge_subadditive hG hConvex (y-x) x.
  rewrite subrK in hTri.
  have hBound:=@norm_minkowski_gauge_inner_ball_bound R V N hN S g r hG hr hBall (y-x).
  rewrite (real_seminorm_subtract hN.1 y x) in hBound; lra.
- have hTri:=minkowski_gauge_subadditive hG hConvex (x-y) y.
  rewrite subrK in hTri.
  have hBound:=@norm_minkowski_gauge_inner_ball_bound R V N hN S g r hG hr hBall (x-y).
  lra.
Qed.
