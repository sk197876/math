(** Federer (1969), 3.2.35, p. 272:
    decompose the actual tube into the source
    closure and its positive-distance strip,
    preserving the original convex source volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  MetricSetDistanceUP MetricSetDistanceClosure MetricDistanceClosureLaws EuclideanConvexClosureVolume
  EuclideanLebesgueDimensions BorelRegularMeasureUP TopologicalBorel MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_tube_volume_splitting]: the
    first equality of the Steiner induction
    in Federer 3.2.35, p. 272, written
    additively to retain defined extended values.
    The source closure is Borel, its actual
    distance is zero precisely there, and
    closing an arbitrary convex source preserves
    its ambient outer volume. No measurability
    of the original source, finite mass or
    hidden hull-difference nullity is assumed. *)
Theorem convex_tube_volume_splitting (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  S!=set0 ->is_inner_convex S ->is_metric_set_distance S d ->0<r ->
  euclidean_lebesgue_measure n [set x|d x<r]=
    (euclidean_lebesgue_measure n S+euclidean_lebesgue_measure n [set x|(0<d x<r)%R])%E.
Proof.
move=>hNonempty hS hD hr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose T:set X:=[set x|d x<r].
have hClosed:@closed [the topologicalType of X] (closure S):=@closed_closure [the topologicalType of X] S.
have hMeasurable:measure_measurable (@euclidean_lebesgue_measure R n) (closure S).
  apply:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_borel_regular R n)); exact:closed_borel_set hClosed.
have hIntersection:T `&` closure S=closure S.
  apply/seteqP; split=>x; first by move=>[_ hx].
  move=>hx; split=>//.
  have hZero:d x=0:=(metric_set_distance_zero_closure hD x).2 hx.
  change (is_true (d x<r)); by rewrite hZero.
have hDifference:T `\` closure S=[set x|(0<d x<r)%R].
  apply/seteqP; split=>x.
  - move=>[hx hOutside]; apply/andP; split; last exact hx.
    exact:(@metric_set_distance_positive_outside_closed R [the metricType R of X]
      (closure S) d (metric_distance_closure_laws hD) x hClosed hOutside).
  - move/andP=>[hPositive hx]; split; first exact hx.
    move=>hc; have hZero: d x=0:=(metric_set_distance_zero_closure hD x).2 hc.
    by rewrite hZero ltxx in hPositive.
have hSplit:=hMeasurable T.
by rewrite hIntersection hDifference (@euclidean_convex_closure_volume R n S hNonempty hS) in hSplit.
Qed.
