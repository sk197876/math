(** General topology supporting Federer (1969), 2.2.10, p. 65: a closed
    subset C of X times N is treated as a metric space. This adapter adds
    the restricted metric to the existing topology on the actual subtype of
    members of C. The narrow subtype_topology import supplies only this
    general topological background. Source context: SuslinSetUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology subtype_topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_subset]: supporting subtype for Federer
    2.2.10, p. 65: its elements are exactly the members
    of A, with the topology induced by inclusion in T. *)
Definition metric_subset (R : realType) (T : metricType R) (A : set T) : Type := set_type A.
HB.instance Definition _ (R : realType) (T : metricType R) (A : set T) :=
  PseudoMetric.copy (metric_subset A) (set_type A).

Section SubsetMetric.
Context (R : realType) (T : metricType R) (A : set T).
Local Notation M := (metric_subset A).

(** Source for [metric_subset_distance_nonnegative]: metric
    background for Federer 2.2.10, p. 65: the distance
    restricted to A remains nonnegative. *)
Lemma metric_subset_distance_nonnegative (x y : M) : 0 <= mdist (val x) (val y).
Proof. exact: mdist_ge0. Qed.

(** Source for [metric_subset_distance_separates]: metric
    background for Federer 2.2.10, p. 65: equality of
    underlying points gives equality of subtype members. *)
Lemma metric_subset_distance_separates (x y : M) :
  mdist (val x) (val y) = 0 -> x = y.
Proof. move=> h; apply: val_inj; exact: (@mdist_positivity R T (val x) (val y) h). Qed.

(** Source for [metric_subset_ball_distance]: subspace-topology
    compatibility supporting Federer 2.2.10, p. 65:
    relative balls are intersections of ambient balls with A. *)
Lemma metric_subset_ball_distance (x : M) r :
  ball x r = [set y : M | mdist (val x) (val y) < r].
Proof.
apply/seteqP; split=> y.
- change (ball (val x) r (val y) -> mdist (val x) (val y) < r).
  by rewrite ballEmdist.
- change (mdist (val x) (val y) < r -> ball (val x) r (val y)).
  by rewrite ballEmdist.
Qed.
HB.instance Definition _ := PseudoMetric_isMetric.Build R M
  metric_subset_distance_nonnegative metric_subset_distance_separates metric_subset_ball_distance.

(** Source for [metric_subset_distanceE]: exposed restricted
    distance identity supporting Federer 2.2.10, p. 65. *)
Lemma metric_subset_distanceE (x y : M) : mdist x y = mdist (val x) (val y).
Proof. by []. Qed.

(** Source for [metric_subset_inclusion_continuous]: supporting
    continuity of the inclusion used to project C in Federer
    2.2.10, p. 65. The inclusion preserves distances. *)
Lemma metric_subset_inclusion_continuous : continuous (fun x : M => (val x : T)).
Proof.
move=> x U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (val x) U) hU.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists e=> // y hy; apply: hb; exact hy.
Qed.
End SubsetMetric.
