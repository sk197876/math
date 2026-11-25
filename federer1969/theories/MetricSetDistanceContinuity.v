(** Federer (1969), 2.2.10, p. 66: continuity of the distance function in
    the closed representation of an open set. Source context:
    MetricSetDistanceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceBasic RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_set_distance_continuous]: supporting continuity for
    Federer 2.2.10, p. 66: the distance to A is continuous because its
    changes are bounded by the input distance. *)
Lemma metric_set_distance_continuous (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) :
  continuous (d : T -> real_line_metric R).
Proof.
move=> x U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (d x : real_line_metric R) U) hU.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x (d @^-1` U))).
exists e=> // y hy; apply: hb.
change (`|d x-d y| < e).
exact: le_lt_trans (@metric_set_distance_lipschitz_one R T A d hd x y) hy.
Qed.
