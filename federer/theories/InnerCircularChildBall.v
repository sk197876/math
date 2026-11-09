(** Federer (1969), 3.3.19, p. 302: each circular
    child disc lies in its original parent. This elementary
    supporting statement uses only the actual inner norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_circular_child_ball_subset]: the
    radius r/q disc centred at z+(1-1/q)r u lies in
    B(z,r), supporting 3.3.19, p. 302. The unit direction,
    nonnegative radius and q>= 1 are the elementary geometry
    hypotheses, rather than a supplied containment premise. *)
Lemma inner_circular_child_ball_subset (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (z u:inner_metric_space hB) (r q:R):
  inner_norm hB u= 1 ->0<=r ->1<=q ->
  metric_closed_ball (z+((1-q^-1)*r)*:u) (r/q) `<=` metric_closed_ball z r.
Proof.
move=>hu hr hq x hx.
have hqp:0<q:=lt_le_trans ltr01 hq.
have hInv:0<q^-1 by rewrite invr_gt0.
have hInv1:q^-1<= 1.
  have hh:=ler_wpM2r (ltW hInv) hq.
  by rewrite mul1r mulfV ?gt_eqF // in hh.
have hScale:0<=(1-q^-1)*r by apply:mulr_ge0=>//;by rewrite subr_ge0.
have hDistance:mdist z (z+((1-q^-1)*r)*:u)=(1-q^-1)*r.
  rewrite inner_metric_distanceE.
  have hD:z-(z+((1-q^-1)*r)*:u)= -(((1-q^-1)*r)*:u) by rewrite opprD addrA subrr add0r.
  by rewrite hD inner_normN inner_normZ hu mulr1 ger0_norm.
have hT:=le_trans (metric_triangle z (z+((1-q^-1)*r)*:u) x)
  (lerD (lexx _) hx).
rewrite hDistance in hT.
have hEq:(1-q^-1)*r+r/q=r by ring.
by rewrite hEq in hT.
Qed.
