(** Federer (1969), 3.3.19, p. 306: the
    actual squared ball condition in local original
    radial coordinates for the final density estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology ring.
From Federer Require Import InnerProductUP Bilinear InnerNorm InnerMetric InnerCapRadiusBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_radial_difference_square]: if an
    original vertex is a= z+d eta, |eta|= 1 and d>=0,
    its actual squared distance from x is
    |x-z|^2+d^2-2d (x-z).eta. This supports
    the last claim in 3.3.19, p. 306. *)
Theorem inner_radial_difference_square (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (z a x eta:inner_metric_space hB) (d:R):
  inner_norm hB eta= 1 ->0<=d ->a= z+d*:eta ->
  (mdist x a)^+2=(inner_norm hB (x-z))^+2+d^+2-2* d* B (x-z) eta.
Proof.
move=>hUnit hd hVertex.
have hVector:x-a=(x-z)-d*:eta by rewrite hVertex opprD addrA.
rewrite inner_metric_distanceE hVector inner_difference_square inner_normZ hUnit mulr1
  (ger0_norm hd) (bilZr (inner_bilinear hB)).
change ((inner_norm hB (x-z))^+2+d^+2-2*(d* B (x-z) eta)=
  (inner_norm hB (x-z))^+2+d^+2-2* d* B (x-z) eta);ring.
Qed.
