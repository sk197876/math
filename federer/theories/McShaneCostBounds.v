(** Federer (1969), 2.10.44, printed p. 202, scalar infimum formula: the
    prescribed costs are bounded below at each new source point. A fixed
    original point and the triangle inequality give the finite lower bound
    needed for existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import RealMetricBackground LipschitzUP McShaneEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [mcshane_cost_lower_bound]: supporting
    finiteness of the infimum in 2.10.44,
    p. 202. For a fixed a0 in S, every
    cost at x is at least f(a0)-L dist(x,a0).
    This includes zero Lipschitz bound. *)
Lemma mcshane_cost_lower_bound (R : realType) (X : metricType R)
    S (f : X -> R) (L : R) (a0 : X) :
  is_metric_lipschitz_bound S (f : X -> real_line_metric R) L -> S a0 ->
  forall x a, S a -> f a0-L*mdist x a0<=f a+L*mdist x a.
Proof.
move=> hSf ha0 x a ha.
have hh := hSf.2 a0 a ha0 ha; rewrite real_line_metric_distanceE in hh.
have hf := le_trans (ler_norm (f a0-f a)) hh.
have ht := metric_triangle a0 x a.
rewrite [mdist a0 x]metric_sym in ht.
have hm := ler_wpM2l hSf.1 ht.
rewrite mulrDr in hm; nra.
Qed.
