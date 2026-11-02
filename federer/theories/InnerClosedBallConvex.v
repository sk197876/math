(** Closed-ball convexity supporting Federer (1969), 2.10.35, p. 197: closed
    spherical generators may be used in the closed convex-cover
    specification of 2.10.4, p. 172. Derive the elementary inner-metric fact
    from the existing abstract norm-ball convexity law. It is supporting
    infrastructure, not a separately numbered assertion of the target. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric InnerConvex
  RealNormUP NormConvexHullDiameter MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_metric_closed_ball_convex]: supporting
    admissibility of closed spherical generators
    in the convex comparison of 2.10.35,
    p. 197. Every real inner-product
    space and every real radius is allowed. *)
Lemma inner_metric_closed_ball_convex (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (a : inner_metric_space hB) (r : R) :
  is_inner_convex (metric_closed_ball a r).
Proof.
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
have he : metric_closed_ball a r=[set x : inner_metric_space hB | inner_norm hB (x-a)<=r].
  by apply/seteqP; split=> x; rewrite /metric_closed_ball /= inner_metric_distanceE -[a-x]opprB inner_normN.
rewrite he; exact: (@norm_ball_inner_convex R V (inner_norm hB) hN a r).
Qed.
