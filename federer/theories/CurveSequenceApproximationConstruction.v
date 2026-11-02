(** Federer (1969), 2.2.15, p. 71: private selection of curves and real
    parameters from the finite approximation condition. The finite sets are
    sequence prefixes; repetitions are harmless. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground FiniteCurveApproximationUP
  CurveSequenceApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [curve_sequence_approximation_exists]: supporting
    existence consequence of the target condition in Federer
    2.2.15, p. 71. Choice selects a curve for each
    finite prefix, and parameters witnessing its approximation. *)
Theorem curve_sequence_approximation_exists (R : realType) (Y : metricType R)
    (y : nat -> Y) : has_finite_curve_approximation Y ->
  exists c, exists t, is_curve_sequence_approximation y c t.
Proof.
move=> h.
have hw n : exists c : real_line_metric R -> Y, continuous c /\
  forall i, (i <= n)%N -> exists t, mdist (y i) (c t) < ((n.+1)%:R)^-1.
  have hf : finite_set (y @` `I_n.+1) := finite_image y (@finite_II n.+1).
  have he : (0 : R) < ((n.+1)%:R)^-1 by rewrite invr_gt0 ltr0n.
  have [c [hc happ]] := h _ hf _ he.
  exists c; split=> // i hi; apply: happ; exists i=> //; exact hi.
pose c n := projT1 (cid (hw n)).
have hc n := projT2 (cid (hw n)).
have ht n i : exists t : R, (i <= n)%N -> mdist (y i) (c n t) < ((n.+1)%:R)^-1.
  case: (leqP i n)=> hin.
  - have [t ht] := (hc n).2 i hin; by exists t.
  - by exists 0.
pose t n i := projT1 (cid (ht n i)).
exists c, t; constructor.
- move=> n; exact: (hc n).1.
- move=> n i hi; exact: (projT2 (cid (ht n i))) hi.
Qed.
