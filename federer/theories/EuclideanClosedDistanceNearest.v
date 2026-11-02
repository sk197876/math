(** Federer (1969), 3.2.34, p. 271: a
    nearest point exists for each point and every
    nonempty closed Euclidean set, without convexity. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNearestUP WhitneyNearestCenters MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_distance_nearest]: the
    choice s in S with f(x)=|s-x| at the
    start of the proof of Federer 3.2.34, p. 271.
    The existing compact-ball nearest-point proof applies
    to arbitrary nonempty closed S, including unbounded
    sets. The abstract distance laws identify its value;
    the witness is local and no convexity is assumed. *)
Lemma euclidean_closed_distance_nearest (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (d:R_n R n->R) x:
  closed S ->S!=set0 ->is_metric_set_distance S d ->
  exists s,S s /\d x=inner_norm (@euclidean_inner_productP R n) (x-s).
Proof.
move=>hClosed hNonempty hDistance.
have [s hs]:=whitney_nearest_point_exists hClosed hNonempty x.
exists s; split; first exact:inner_nearest_member_law hs.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact:(metric_set_distance_lower hDistance x (inner_nearest_member_law hs)).
- apply:(@metric_set_distance_greatest R
    (inner_metric_space (@euclidean_inner_productP R n)) S d hDistance x
    (inner_norm (@euclidean_inner_productP R n) (x-s))).
  move=>z hz; exact:(inner_nearest_minimal_law hs hz).
Qed.
