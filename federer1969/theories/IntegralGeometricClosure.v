(** Supporting closure comparison for Federer (1969), 2.10.5(2), p. 173:
    open convex and closed convex generators give the same Q_t. This module
    proves the direction obtained by closing an open generator. Its
    projected volumes are unchanged by the already proved open convex
    closure identity, so its actual extended norm and normalized cost are
    unchanged, also at exponent infinity. The converse enlargement direction
    is a separate obligation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvexNeighbourhoods
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricMeasureUP
  ProjectionMeasureUP ProjectedVolumeMeasurability ProjectedVolumePointwiseClosure
  BorelClosedProjection TopologicalBorel MetricDiameter MetricDiameterClosure
  CaratheodoryFamilyReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_open_convex_closure]:
    supporting equality of the costs of an open
    convex set and its closure in Federer 2.10.5(2),
    p. 173. The sets may be unbounded or empty;
    the norm uses their equal actual projected volumes. *)
Theorem integral_geometric_gauge_open_convex_closure (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (U : set (inner_metric_space (@euclidean_inner_productP R n))) (t : \bar R) :
  open U -> @InnerConvex.is_inner_convex R (R_n R n) U ->
  @integral_geometric_gauge R n m hmn t (closure U)=
    @integral_geometric_gauge R n m hmn t U.
Proof.
move=> hU hc.
have he : projected_volume_function (m:=m) (closure U)=projected_volume_function (m:=m) U.
  apply: funext=> p; exact: projected_volume_function_open_convex_closure.
by rewrite /integral_geometric_gauge he.
Qed.

(** Source for [closed_convex_integral_geometric_le_open]:
    supporting inequality from closed-generator Q_t
    to open-generator Q_t in Federer 2.10.5(2),
    p. 173. Close each open convex generator,
    preserving diameter and cost. The reverse
    inequality is not a premise or conclusion here. *)
Theorem closed_convex_integral_geometric_le_open (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t ->
  @closed_convex_integral_geometric_measure R n m hmn t A<=
    @convex_integral_geometric_measure R n m hmn t A.
Proof.
move=> ht.
apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
  (open_convex_euclidean_sets R n) (closed_convex_euclidean_sets R n)
  (fun j => val j) (fun j => val j)
  (fun j => @integral_geometric_gauge R n m hmn t (val j))
  (fun j => @integral_geometric_gauge R n m hmn t (val j))
  (@convex_integral_geometric_measure R n m hmn t)
  (@closed_convex_integral_geometric_measure R n m hmn t)
  (@convex_integral_geometric_measure_specification R n m hmn t)
  (@closed_convex_integral_geometric_measure_specification R n m hmn t) _ _ A).
- move=> j; apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)).
  exact: metric_borel_suslin (closed_borel_set (set_valP j).1).
- move=> j.
  pose k : closed_convex_euclidean_sets R n :=
    @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) =>
      B \in [set B : set (inner_metric_space (@euclidean_inner_productP R n)) |
        closed B /\ @InnerConvex.is_inner_convex R (R_n R n) B])
      (closure (val j)) (mem_set (conj (@closed_closure
        (inner_metric_space (@euclidean_inner_productP R n)) (val j))
        (@inner_convex_closure R (R_n R n) (@euclidean_inner_product R n)
          (@euclidean_inner_productP R n) (val j) (set_valP j).2))).
  exists k; split; first exact: (@subset_closure _ (val j)).
  split.
  + change (extended_metric_diameter (closure (val j))<=extended_metric_diameter (val j)).
    by rewrite extended_metric_diameter_closure.
  + change (@integral_geometric_gauge R n m hmn t (closure (val j))<=
      @integral_geometric_gauge R n m hmn t (val j)).
    by rewrite (@integral_geometric_gauge_open_convex_closure R n m hmn (val j) t
      (set_valP j).1 (set_valP j).2).
Qed.
