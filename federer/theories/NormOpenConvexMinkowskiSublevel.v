(** Federer (1969), 3.2.35, p. 271:
    the original open convex body is exactly
    the strict unit sublevel of its actual gauge. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealNormUP NormMetric InnerConvex MinkowskiGaugeUP
  MinkowskiGaugeSublevel NormOpenRadialRoom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_convex_minkowski_sublevel]:
    supporting the boundary representation in Federer
    3.2.35, p. 271. Original openness gives
    radial room and hence g<1; original convexity
    and zero membership recover S from g<1.
    The source is unchanged and no closure-
    membership premise is substituted. *)
Theorem norm_open_convex_minkowski_sublevel (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set (real_norm_metric_space hN)) g:
  @is_minkowski_gauge R V S g ->open S ->@is_inner_convex R V S ->S 0 ->
  forall x:V,S x <->g x<1.
Proof.
move=>hG hOpen hConvex hZero x; split.
- move=>hx; have [c [hc hS]]:=@norm_open_radial_room R V N hN S x hOpen hx.
  exact (@minkowski_gauge_radial_room_sublevel R V S g x c hG hc hS).
- exact (@minkowski_gauge_strict_sublevel_member R V S g x hG hConvex hZero).
Qed.
