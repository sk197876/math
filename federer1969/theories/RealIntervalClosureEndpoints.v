(** Federer (1969), 2.2.9, p. 65: interval children have disjoint open sets,
    while their closures may meet. These endpoint facts support a regression
    for that distinction in the real-line refinement. Source context:
    NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_interval_endpoint_step]: local scalar
    support for endpoint closure in Federer 2.2.9, p. 65:
    choose a positive step smaller than both interval length
    and neighborhood radius. *)
Lemma real_interval_endpoint_step (R : realType) (l r : R) :
  0 < l -> 0 < r -> exists q, 0 < q /\ q < l /\ q < r.
Proof.
move=> hl hr; exists (Order.min (l/2) (r/2)); split.
- by rewrite lt_min !divr_gt0 // ltr0n.
- split.
  + apply: le_lt_trans (_ : Order.min (l/2) (r/2) <= l/2) _.
      by rewrite ge_min lexx.
    by rewrite ltr_pdivrMr ?ltr0n // -{1}[l]mulr1 (ltr_pM2l hl) ltr1n.
  + apply: le_lt_trans (_ : Order.min (l/2) (r/2) <= r/2) _.
      by rewrite ge_min lexx orbT.
    by rewrite ltr_pdivrMr ?ltr0n // -{1}[r]mulr1 (ltr_pM2l hr) ltr1n.
Qed.

(** Source for [real_open_interval_left_endpoint_closure]:
    supporting endpoint closure for the interval refinement in
    Federer 2.2.9, p. 65: the left endpoint is a limit
    of interior points. This is general real topology, not an
    additional claim of disjoint child closures. *)
Lemma real_open_interval_left_endpoint_closure (R : realType) (a b : R) :
  a < b -> closure (real_open_interval a b) a.
Proof.
move=> hab B hB.
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP
  (a : real_line_metric R) B) hB.
have hl : 0 < b-a by rewrite subr_gt0.
have [q [hq [hql hqr]]] := real_interval_endpoint_step hl hr.
exists (a+q); split.
- split; first by rewrite ltrDl.
  by rewrite -ltrBrDl.
- apply: hb; change (`|a-(a+q)| < r); rewrite opprD addrA subrr add0r normrN.
  by rewrite ger0_norm ?(ltW hq).
Qed.

(** Source for [real_open_interval_right_endpoint_closure]:
    supporting endpoint closure for Federer 2.2.9, p. 65:
    the right endpoint is approached by interior points from
    the left, allowing adjacent child closures to meet. *)
Lemma real_open_interval_right_endpoint_closure (R : realType) (a b : R) :
  a < b -> closure (real_open_interval a b) b.
Proof.
move=> hab B hB.
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP
  (b : real_line_metric R) B) hB.
have hl : 0 < b-a by rewrite subr_gt0.
have [q [hq [hql hqr]]] := real_interval_endpoint_step hl hr.
exists (b-q); split.
- split.
  + by rewrite ltrBrDl -ltrBrDr.
  + by rewrite ltrBlDl ltrDr.
- apply: hb; change (`|b-(b-q)| < r); rewrite subKr.
  by rewrite ger0_norm ?(ltW hq).
Qed.
