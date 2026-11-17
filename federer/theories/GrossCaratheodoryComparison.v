(** Federer (1969), 2.10.6, p. 173:
    Gross measure is at most Caratheodory projection
    measure, directly from the preceding covering families. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ProjectionMeasureUP ProjectionMeasure
  ProjectedVolumeGauge BorelCoverCostUP CaratheodoryFamilyReplacement TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_caratheodory_projection_bound]:
    direct vertical G^m<=C^m edge of
    the diagram in Federer 2.10.6,
    p. 173. Every original open convex
    generator is Borel, with precisely the same
    projected-volume cost and metric diameter.
    The already proved covering-family replacement theorem
    compares the two original constructions. Arbitrary
    targets and infinite masses remain. *)
Theorem gross_caratheodory_projection_bound (R : realType) n m (hMN : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @gross_measure R n m A<=@caratheodory_projection_measure R n m A.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R n).
apply: (@caratheodory_family_replacement R [the metricType R of X]
  (open_convex_euclidean_sets R n) (@borel_metric_sets R [the metricType R of X])
  (fun j => val j) (fun j => val j)
  (fun j => projected_volume_gauge m (val j)) (fun j => projected_volume_gauge m (val j))
  (@caratheodory_projection_measure R n m) (@gross_measure R n m)
  (caratheodory_projection_measure_specification R n m) (gross_measure_specification R n m) _ _ A).
- move=> j; exact: projected_volume_gauge_nonnegative hMN.
- move=> j.
  pose k : @borel_metric_sets R [the metricType R of X] :=
    exist _ (val j) (mem_set (open_borel_set (set_valP j).1)).
  exists k; split; first by move=> x hx.
  by split; exact: lexx.
Qed.
