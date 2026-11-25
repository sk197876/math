(** Federer (1969), 3.4.8(10), p. 331:
    choose a smaller convex prefix neighbourhood
    whose full inverse image is connected.
    Apply the existing norm-ball, affine-preimage
    and convex-connectedness theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormLinearDomainLaws InnerConvex AffineMaps AffineConvexPreimage NormConvexConnected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_prefix_ball_neighbourhood]:
    the common domain p_m inverse(Y)
    in 3.4.8(10), p. 331, may
    use a prefix ball. Its cylinder
    is open and connected; every suffix
    coordinate remains unrestricted. *)
Theorem norm_prefix_ball_neighbourhood (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (projection:Hom X Y) (U:set Y):
  norm_bounded_linear NX NY projection ->
  @open (real_norm_metric_space hNY) U ->U 0 ->
  exists r:R,0<r /\(forall y,NY y<r ->U y) /\
    @open (real_norm_metric_space hNX) [set x|NY (projection x)<r] /\
    @connected (real_norm_metric_space hNX) [set x|NY (projection x)<r].
Proof.
move=>hProjection hOpen hOrigin.
have hNeighbourhood:=hOpen;rewrite openE in hNeighbourhood.
have [r [hR hInside]]:=(@norm_domain_interior_neighbourhood R Y NY hNY U 0).2
  (hNeighbourhood 0 hOrigin).
have hBall:is_inner_convex [set y:Y|NY y<r].
  move=>y z hy hz t ht ht1.
  have hy0:NY (y-0)<r by rewrite subr0.
  have hz0:NY (z-0)<r by rewrite subr0.
  have h:=@norm_open_ball_convex R Y NY hNY 0 r y z hy0 hz0 t ht ht1.
  by rewrite subr0 in h.
have hAffine:is_affine_map projection.
  by move=>x y a b _;rewrite linearD !linearZ.
have hConvex:=@affine_preimage_inner_convex R X Y projection [set y|NY y<r] hAffine hBall.
have hInterior x (hx:NY (projection x)<r):
    norm_domain_interior NX [set z|NY (projection z)<r] x.
  apply:(@norm_bounded_linear_preimage_interior R X Y NX NY hNX projection [set y|NY y<r] x hProjection).
  have hx0:NY (projection x-0)<r by rewrite subr0.
  have [s [hS hLocal]]:=@norm_open_ball_domain_interior R Y NY hNY 0 r (projection x) hx0.
  exists s;split;first exact:hS.
  move=>z hz;have h:=hLocal z hz;by rewrite subr0 in h.
have hCylinderOpen:@open (real_norm_metric_space hNX) [set x|NY (projection x)<r].
  rewrite openE=>x hx;exact:((@norm_domain_interior_neighbourhood R X NX hNX _ x).1 (hInterior x hx)).
exists r;split;first exact:hR.
split;first by move=>y hy;have h:=hInside y hy;rewrite add0r in h.
split;first exact:hCylinderOpen.
exact:(@norm_inner_convex_connected R X NX hNX _ hConvex).
Qed.
