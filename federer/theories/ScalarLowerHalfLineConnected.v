(** Federer (1969), 3.4.5, p. 321: connectedness
    of the original real axis below the flat endpoint,
    supporting the analytic identity argument of 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealNormUP NormMetric InnerConvex NormConvexConnected HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_lower_half_line_connected]: each
    original lower half-axis is convex and hence connected,
    supporting the local/global example in 3.4.5, p. 321. *)
Theorem scalar_lower_half_line_connected (R:realType) (b:R):
  @connected (real_norm_metric_space (@scalar_absolute_value_norm R)) [set z:R^o|z<b].
Proof.
apply:norm_inner_convex_connected=>x y hx hy t ht0 ht1.
change ((1-t)*x+t*y<b).
case:(eqVneq t 0)=>[->|ht].
- by rewrite subr0 mul1r mul0r addr0.
- have hPositive:0<t by rewrite lt_neqAle eq_sym ht ht0.
  have hFirst:(1-t)*x<=(1-t)*b.
    apply:ler_wpM2l;[by rewrite subr_ge0|exact:ltW hx].
  have hSecond:t*y<t*b by rewrite ltr_pM2l.
  have hBound:=ler_ltD hFirst hSecond.
  have hEnd:(1-t)*b+t*b=b by rewrite -mulrDl subrK mul1r.
  by rewrite hEnd in hBound.
Qed.
