(** Federer (1969), 3.3.19, p. 303: the
    radial retraction fixes each outward normal ray at
    its point on the original ball. Prove its nearest
    point property directly from actual metric triangles. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import InnerProductUP InnerNorm InnerMetric MetricClosedBalls InnerNearestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_ball_radial_nearest]: the actual
    point z+r u is nearest to z+d u in the
    original closed ball whenever u is unit and
    0<=r<=d, supporting the radial formula in
    3.3.19, p. 303. Auxiliary units are
    local; zero radius is retained. *)
Theorem inner_ball_radial_nearest (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (z u:inner_metric_space hB) (r d:R):
  inner_norm hB u= 1 ->0<=r ->r<=d ->
  is_inner_nearest hB (z+d*:u) (metric_closed_ball z r) (z+r*:u).
Proof.
move=>hu hr hrd.
have hd:0<=d by lra.
have hDifference (a b:R):(z+a*:u)-(z+b*:u)=(a-b)*:u.
  by rewrite opprD addrACA subrr add0r -scalerBl.
have hCentre a:(z+a*:u)-z=a*:u by rewrite addrAC subrr add0r.
have hRadius:mdist z (z+r*:u)=r.
  by rewrite metric_sym inner_metric_distanceE hCentre inner_normZ hu mulr1 ger0_norm.
have hOuter:mdist (z+d*:u) z=d.
  by rewrite inner_metric_distanceE hCentre inner_normZ hu mulr1 ger0_norm.
have hNear:inner_norm hB ((z+d*:u)-(z+r*:u))=d-r.
  have hNonnegative:0<=d-r by lra.
  by rewrite hDifference inner_normZ hu mulr1 ger0_norm.
constructor;first by change (is_true (mdist z (z+r*:u)<=r));rewrite hRadius.
move=>y hy;rewrite hNear.
have hTriangle:=metric_triangle (z+d*:u) y z.
rewrite hOuter in hTriangle.
have hy':mdist (y:inner_metric_space hB) z<=r by rewrite metric_sym;exact hy.
change (is_true (d-r<=mdist (z+d*:u) y));lra.
Qed.
