(** Federer (1969), 3.3.19, p. 306: actual
    nearby original child centres have radial directions
    close to that of the original test-ball vertex. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp topology lra ring.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Nearby.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation E:=(inner_metric_space hB).
Local Notation N:=(inner_norm hB).

(** Source for [inner_nearby_radial_directions_bound]: if
    a= z+d eta, |eta|= 1, |d-c|<=h and the
    original centre z+cu is within t+h of a, then
    c|u-eta|<=t+2h. This elementary local radial
    estimate supports the final density proof of
    3.3.19, p. 306. *)
Theorem inner_nearby_radial_directions_bound (z a u eta:E) (d c t h:R):
  N eta= 1 ->a= z+d*:eta ->0<c ->`|d-c|<=h ->
  mdist (z+c*:u) a<=t+h ->c* N (u-eta)<=t+2* h.
Proof.
move=>hUnit hVertex hc hDeficit hNear.
have hVector:c*:(u-eta)=((z+c*:u)-a)+(d-c)*:eta.
  rewrite hVertex opprD scalerBr scalerBl.
  have hCancel:((z+c*:u)+(-z+ -(d*:eta)))+(d*:eta-c*:eta)=c*:u-c*:eta.
    by rewrite (addrACA z (c*:u) (-z) (-(d*:eta))) subrr add0r addrA subrK.
  exact:esym hCancel.
have hTriangle:= inner_norm_triangle hB ((z+c*:u)-a) ((d-c)*:eta).
rewrite -hVector inner_normZ (ger0_norm (ltW hc)) inner_normZ hUnit mulr1
  -(@inner_metric_distanceE R V B hB (z+c*:u) a) in hTriangle.
lra.
Qed.
End Nearby.
