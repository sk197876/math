(** Federer (1969), 3.2.35, p. 272:
    replacing a source by its closure preserves
    its actual distance, for use of 3.2.34. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_distance_closure_laws]:
    supporting the closed-source application of
    3.2.34 inside Federer 3.2.35, p. 272.
    Closure points have actual distance zero.
    The proved Lipschitz inequality extends the
    lower law there, and closure containment
    gives the converse greatest-lower-bound law.
    No regularity or measurability is assumed. *)
Lemma metric_distance_closure_laws (R:realType) (X:metricType R) (S:set X) d:
  is_metric_set_distance S d ->is_metric_set_distance (closure S) d.
Proof.
move=>hD; constructor.
- move=>x a ha.
  have hZero: d a=0:=(metric_set_distance_zero_closure hD a).2 ha.
  have hh:=metric_set_distance_subtract_bound hD x a.
  by rewrite hZero subr0 in hh.
- move=>x r hLower.
  apply:(@metric_set_distance_greatest R X S d hD x r)=>a ha.
  exact:hLower a (subset_closure ha).
Qed.
