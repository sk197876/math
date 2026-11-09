(** Federer (1969), 3.3.19, p. 302: the
    original closed disc meets a closed halfplane only if
    its centre has signed normal coordinate at least minus
    its radius. Prove this from actual inner-metric laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric MetricClosedBalls Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_halfplane_ball_centre_bound]: actual
    unit-normal coordinate bound supporting the halfplane
    assertion of 3.3.19, p. 302. The actual
    meeting point discharges all radius and distance inputs;
    zero radii are retained in this supporting lemma. *)
Lemma inner_halfplane_ball_centre_bound (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (u z c x:inner_metric_space hB) (r:R):
  inner_norm hB u= 1 ->metric_closed_ball c r x ->0<=B u (x-z) ->
  -r<=B u (c-z).
Proof.
move=>hu hx hHalf.
have hCauchy:=inner_cauchy hB u (c-x).
rewrite hu mul1r -inner_metric_distanceE in hCauchy.
change (is_true (mdist c x<=r)) in hx.
have hAbsolute:`|B u (c-x)|<=r:=le_trans hCauchy hx.
have /andP[hLower hUpper]:(-r<=B u (c-x)<=r) by move:hAbsolute;rewrite ler_norml.
have hDifference:c-z=(c-x)+(x-z) by rewrite addrA subrK.
rewrite hDifference (bilDr (inner_bilinear hB));lra.
Qed.
