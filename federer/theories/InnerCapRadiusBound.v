(** Federer (1969), 3.3.19, p. 305: the elementary
    actual closed-cap radius estimate needed to pass from
    cap masses to the original strict cones. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import InnerProductUP Bilinear InnerNorm InnerNormInequalities InnerMetric MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Radius.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation E:=(inner_metric_space hB).
Local Notation N:=(inner_norm hB).

(** Source for [inner_difference_square]: expansion of the
    original squared Euclidean distance, from 1.7.1, p. 28,
    supporting the cap geometry in 3.3.19, p. 305. *)
Lemma inner_difference_square (x y:V):
  (N (x-y))^+2=(N x)^+2+(N y)^+2-2* B x y.
Proof.
rewrite !inner_norm_sqr (bilBl (inner_bilinear hB))
  !(bilBr (inner_bilinear hB)) (inner_symmetric hB y x).
ring.
Qed.

(** Source for [inner_cap_centre_radius_bound]: a unit-normal
    cap of radius r, threshold rc and c^2+s^2= 1 lies
    in the ball of radius rs about its section centre rcu.
    All cap boundaries are retained. This supports the corrected
    strict-cone passage in 3.3.19, p. 305. *)
Lemma inner_cap_centre_radius_bound (z u x:E) (r c s:R):
  0<=r ->0<=c ->0<=s ->c^+2+s^+2= 1 ->N u= 1 ->
  metric_closed_ball z r x ->r* c<=B (x-z) u ->
  N ((x-z)-(r* c)*:u)<=r* s.
Proof.
move=>hr hc hs hUnit hu hx hCap.
have hNorm:0<=N (x-z):= inner_norm_nonnegative hB _.
have hUpper:N (x-z)<=r.
  by rewrite -inner_metric_distanceE metric_sym.
have hSquare:(N (x-z))^+2<=r^+2 by rewrite ler_sqr.
have hScaled:= ler_wpM2l (mulr_ge0 hr hc) hCap.
have hExpansion:(N ((x-z)-(r* c)*:u))^+2=
    (N (x-z))^+2+(r* c)^+2-2*(r* c)* B (x-z) u.
  rewrite inner_difference_square inner_normZ hu mulr1
    (ger0_norm (mulr_ge0 hr hc)) (bilZr (inner_bilinear hB)).
  change ((N (x-z))^+2+(r* c)^+2-2*((r* c)* B (x-z) u)=
    (N (x-z))^+2+(r* c)^+2-2*(r* c)* B (x-z) u);ring.
rewrite -(ler_sqr (inner_norm_nonnegative hB _) (mulr_ge0 hr hs)) hExpansion.
have hUnitScaled:= congr1 (fun t:R=>r^+2* t) hUnit.
nra.
Qed.

(** Source for [inner_cap_boundary_radius_bound]: if eta is
    a unit boundary direction with eta.u= c, every actual
    point of the closed cap is within 2rs of z+r eta.
    This is the geometric radius estimate underlying
    3.3.19, p. 305, with equality allowed. *)
Theorem inner_cap_boundary_radius_bound (z eta u x:E) (r c s:R):
  0<=r ->0<=c ->0<=s ->c^+2+s^+2= 1 ->N eta= 1 ->N u= 1 ->
  B eta u= c ->metric_closed_ball z r x ->r* c<=B (x-z) u ->
  mdist x (z+r*:eta)<=2* r* s.
Proof.
move=>hr hc hs hUnit hEta hu hPair hx hCap.
have hNear:= inner_cap_centre_radius_bound hr hc hs hUnit hu hx hCap.
have hBoundaryBall:metric_closed_ball z r (z+r*:eta).
  change (is_true (mdist z (z+r*:eta)<=r)).
  by rewrite metric_sym inner_metric_distanceE addrAC subrr add0r
    inner_normZ hEta mulr1 (ger0_norm hr).
have hBoundaryCap:r* c<=B ((z+r*:eta)-z) u.
  rewrite addrAC subrr add0r (bilZl (inner_bilinear hB)) hPair;exact:lexx.
have hBoundary:= inner_cap_centre_radius_bound hr hc hs hUnit hu hBoundaryBall hBoundaryCap.
have hTriangle:= metric_triangle x (z+(r* c)*:u) (z+r*:eta).
have hVector:x-(z+(r* c)*:u)=(x-z)-(r* c)*:u by rewrite opprD addrA.
have hBoundaryVector:(z+r*:eta)-(z+(r* c)*:u)=
    ((z+r*:eta)-z)-(r* c)*:u by rewrite opprD addrA.
rewrite (metric_sym (z+(r* c)*:u) (z+r*:eta)) !inner_metric_distanceE
  hVector hBoundaryVector in hTriangle.
rewrite -inner_metric_distanceE in hTriangle.
lra.
Qed.
End Radius.
