(** Federer (1969), 2.10.40, printed p. 200: the parallelogram identity
    shrinks the common scale of the midpoint of two different feasible
    centres. This scalar supporting lemma verifies the printed square-root
    scale uniformly over radii r<=mu. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_midpoint_strict_scale]: supporting
    t=sqrt(c^2-d^2/(4 mu^2)) calculation in
    2.10.40, p. 200. A nonzero separation d
    gives a strictly smaller nonnegative scale, and
    the estimate applies uniformly to every prescribed radius. *)
Lemma weighted_midpoint_strict_scale (R : realType) (c mu d : R) :
  0<=c -> 0<mu -> 0<d -> d^+2<=4*mu^+2*c^+2 ->
  exists t : R, 0<=t /\ t<c /\ forall r z : R,
    0<r -> r<=mu -> 0<=z -> 4*z^+2+d^+2<=4*r^+2*c^+2 -> z<=r*t.
Proof.
move=> hc hmu hd hbound.
pose den := 4*mu^+2.
have hden : 0<den by rewrite /den mulr_gt0 ?ltr0n // exprn_gt0.
have hden0 : den!=0 by rewrite (gt_eqF hden).
pose delta := d^+2/den.
have hdelta : 0<delta by rewrite /delta divr_gt0 // exprn_gt0.
have heq : den*delta=d^+2 by rewrite /delta mulrCA mulfV // mulr1.
have hdc : delta<=c^+2.
  rewrite /delta ler_pdivrMr //; rewrite mulrC /den; exact hbound.
pose t := Num.sqrt (c^+2-delta).
have ht : 0<=t := sqrtr_ge0 _.
have hsq : t^+2=c^+2-delta by rewrite /t sqr_sqrtr // subr_ge0.
have htc : t<c by nra.
exists t; split=> //; split=> // r z hr hrmu hz hmid.
have hrr : r^+2<=mu^+2 by rewrite (ler_sqr (ltW hr) (ltW hmu)).
have hgap := ler_wpM2r (ltW hdelta) hrr.
have hrt : 0<=r*t := mulr_ge0 (ltW hr) ht.
rewrite -(ler_sqr hz hrt) exprMn.
rewrite /den in heq; nra.
Qed.
