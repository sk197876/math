(** Federer (1969), 3.4.12, p. 339: connected half-planes
    support the complex covering qualification. This connection uses
    the existing convex-connectedness theorem; it imposes no
    completeness or finite-dimensional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerConvex NormConvexConnected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_positive_functional_connected]: an actual
    strict positive linear half-space is convex and connected,
    supporting the complex covering example for 3.4.12, p. 339. *)
Theorem norm_positive_functional_connected (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (f:Hom X R^o):
  @connected (real_norm_metric_space hNX) [set x|0<f x].
Proof.
apply:norm_inner_convex_connected=>x y hx hy t ht0 ht1.
change (is_true (0<f ((1-t)*:x+t*:y))).
rewrite linearD !linearZ /=.
change (is_true (0<(1-t)*f x+t*f y)).
case:(eqVneq t 0)=>[->|ht].
- by rewrite subr0 mul1r mul0r addr0.
- have hPositive:0<t by rewrite lt_neqAle eq_sym ht ht0.
  have hFirst:0<=(1-t)*f x.
    apply:mulr_ge0;[by rewrite subr_ge0|exact:ltW hx].
  have hSecond:0<t*f y by rewrite mulr_gt0.
  have hSum:=ler_ltD hFirst hSecond.
  by rewrite add0r in hSum.
Qed.
