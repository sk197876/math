(** Metric topology supporting Federer (1969), 2.3.7, pp. 77–78: the
    pair-distance map is continuous. Source context:
    UniformPartialConvergenceUP.v. The bounds below are proved locally from
    the triangle inequality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [metric_pair_distance_difference_bound]: supporting
    two-variable triangle estimate for the distance sets C_{i,j}
    in Federer 2.3.7, p. 77. *)
Lemma metric_pair_distance_difference_bound (R : realType) (Y : metricType R)
    (a b c d : Y) : mdist a b - mdist c d <= mdist a c + mdist b d.
Proof.
rewrite lerBlDr.
have hb := le_trans (metric_triangle a c b)
  (lerD (lexx (mdist a c)) (metric_triangle c d b)).
rewrite (metric_sym d b) in hb.
by rewrite [mdist c d + mdist b d]addrC addrA in hb.
Qed.

(** Source for [metric_pair_distance_change_bound]: supporting absolute
    variation bound for the continuous distance map used in Federer 2.3.7,
    pp. 77–78 *)
Lemma metric_pair_distance_change_bound (R : realType) (Y : metricType R)
    (a b c d : Y) : `|mdist a b - mdist c d| <= mdist a c + mdist b d.
Proof.
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (metric_sym a c) (metric_sym b d).
  exact: metric_pair_distance_difference_bound.
- exact: metric_pair_distance_difference_bound.
Qed.

(** Source for [metric_pair_distance_continuous]: Supporting Federer 2.3.7,
    pp. 77–78. *)
Lemma metric_pair_distance_continuous (R : realType) (Y : metricType R) :
  continuous (fun p : Y * Y => (mdist p.1 p.2 : real_line_metric R)).
Proof.
move=> [a b] U hU.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (mdist a b : real_line_metric R) U) hU.
have hh : 0 < e/2 by rewrite divr_gt0 // ltr0n.
exists ([set c | mdist a c < e/2], [set d | mdist b d < e/2]).
- split.
  + apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)).
    exists (e/2)=> // c hc; exact hc.
  + apply: (proj2 (metricType_numDomainType.nbhs_mdistP b _)).
    exists (e/2)=> // d hd; exact hd.
- move=> [c d] [hc hd]; apply: hball.
  change (`|mdist a b-mdist c d| < e).
  apply: le_lt_trans (metric_pair_distance_change_bound a b c d) _.
  have h := ltrD hc hd; by rewrite -splitr in h.
Qed.
