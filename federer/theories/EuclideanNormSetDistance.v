(** Federer (1969), 3.2.35, p. 272:
    a ball is the actual distance tube of
    its centre, used for normalization constants. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_norm_set_distance]: supporting
    ball normalization for Steiner's coefficients,
    Federer 3.2.35, p. 272, using the
    distance convention of 3.2.34, p. 271.
    The actual Euclidean norm satisfies precisely
    the independent distance laws for {0}. *)
Lemma euclidean_norm_set_distance (R:realType) n:
  @is_metric_set_distance R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    [set 0] (inner_norm (@euclidean_inner_productP R n)).
Proof.
constructor.
- move=>x a ->; by rewrite inner_metric_distanceE subr0.
- move=>x r hLower.
  have hh:=hLower 0 erefl; by rewrite inner_metric_distanceE subr0 in hh.
Qed.
