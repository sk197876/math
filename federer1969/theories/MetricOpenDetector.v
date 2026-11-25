(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground MetricSetDistanceUP MetricSetDistanceSealed
  MetricSetDistanceBasic MetricSetDistanceContinuity MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_metric_open_detector]: supporting general-topology
    specification for the bounded-support test lattice in Federer 2.9.10, p.
    157. A continuous function in [0,1] is positive exactly on the given
    open set. This is the distance-to-complement argument of 2.2.10, p. 66,
    also. *)
Definition is_metric_open_detector (R : realType) (X : metricType R)
    (U : set X) (g : X -> R) :=
  continuous (g : X -> real_line_metric R) /\
  (forall x, 0<=g x<=1) /\ (forall x, U x <-> 0<g x).

(** Source for [metric_open_detector_exists]: supporting existence
    for the general-topology step in Federer 2.9.10, p. 157.
    Cap the abstract distance to the nonempty closed complement
    at one; for the whole space use the constant one. The
    distance construction remains behind its sealed infimum laws. *)
Theorem metric_open_detector_exists (R : realType) (X : metricType R) (U : set X) :
  open U -> exists g : X -> R, is_metric_open_detector U g.
Proof.
move=> hU; case: (pselect ((~` U) !=set0))=> [hne|hempty].
- pose d := @MetricSetDistance.value R X (~` U) hne.
  have hd := @MetricSetDistance.laws R X (~` U) hne.
  exists (fun x => Num.min (d x) 1); split.
  + move=> x; apply: (@continuous_min R X d (fun _ => 1) x).
    * exact (@metric_set_distance_continuous R X (~` U) d hd x).
    * exact: cvg_cst.
  + split.
    * move=> x; apply/andP; split.
      -- by rewrite le_min (metric_set_distance_nonnegative hd x) ler01.
      -- by rewrite ge_min lexx orbT.
    * move=> x; split.
      -- move=> hx; rewrite lt_min ltr01 andbT.
         apply: (@metric_set_distance_positive_outside_closed R X (~` U) d hd x (open_closedC hU)).
         by move=> hn; exact: hn hx.
      -- move=> hp; apply: contrapT=> hn.
         by move: hp; rewrite /d (metric_set_distance_member hd hn) (min_l ler01) ltxx.
- exists (fun _ => 1); split; first by move=> x; exact: cvg_cst.
  split; first by move=> x; rewrite ler01 lexx.
  move=> x; split=> // _; apply: contrapT=> hn; apply: hempty; by exists x.
Qed.
