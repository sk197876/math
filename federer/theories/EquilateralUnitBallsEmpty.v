(** Federer (1969), 2.10.44, printed p. 202, first example: no point eta in
    R^2 is within Euclidean distance one of all three prescribed target
    points. The first two squared constraints force both coordinates of eta
    to vanish; the third would require 3<=1. This expands the printed
    obstruction directly in the actual Euclidean metric. Source context:
    KirszbraunCorners.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric PlanePairNormGeometry KirszbraunCorners.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [kirszbraun_three_unit_balls_empty]: direct
    no-eta assertion in 2.10.44, p. 202,
    for the actual printed three target points.
    It is independent of any chosen source map
    and uses the Euclidean squared-distance laws. *)
Theorem kirszbraun_three_unit_balls_empty (R : realType) :
  ~ exists p : inner_metric_space (@euclidean_inner_productP R 2),
    mdist p (kirszbraun_equilateral_first R)<=1 /\
    mdist p (kirszbraun_equilateral_second R)<=1 /\
    mdist p (kirszbraun_equilateral_third R)<=1.
Proof.
move=> [p [h1 [h2 h3]]].
have h1s : mdist p (kirszbraun_equilateral_first R)^+2<=(1:R)^+2.
  by rewrite (ler_sqr (mdist_ge0 _ _) ler01).
have h2s : mdist p (kirszbraun_equilateral_second R)^+2<=(1:R)^+2.
  by rewrite (ler_sqr (mdist_ge0 _ _) ler01).
have h3s : mdist p (kirszbraun_equilateral_third R)^+2<=(1:R)^+2.
  by rewrite (ler_sqr (mdist_ge0 _ _) ler01).
rewrite expr1n euclidean_plane_squared_distance_coordinates
  /kirszbraun_equilateral_first !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate in h1s.
rewrite expr1n euclidean_plane_squared_distance_coordinates
  /kirszbraun_equilateral_second !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate in h2s.
rewrite expr1n euclidean_plane_squared_distance_coordinates
  /kirszbraun_equilateral_third !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate in h3s.
have hxpos := sqr_ge0 (p ord0).
have hypos := sqr_ge0 (p ord_max).
have hx0 : p ord0=0 by nra.
have hy0 : p ord_max=0 by nra.
have hsqrt : (Num.sqrt (3:R))^+2= 3 by rewrite sqr_sqrtr // ler0n.
rewrite hx0 hy0 in h3s; nra.
Qed.
