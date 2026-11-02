(** Convex projected-volume comparison supporting Federer (1969), 2.10.35,
    p. 197. In equal dimensions the projected cost is Lebesgue volume.
    Closed balls are convex, so the closed convex-cover alternative of
    2.10.4, p. 172, gives an upper bound by spherical measure. This also
    supplies the printed Q_t comparison after the full-dimensional integral
    gauge is identified. Source context: FullDimensionProjections.v and
    EuclideanHausdorffLebesgue.v. This is a supporting consequence for C^n,
    not an extra equality inserted into the printed list of 2.10.35. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions InnerConvex InnerClosedBallConvex
  FullDimensionProjectedVolume ProjectedVolumeGauge ProjectionMeasureUP ProjectionMeasure ProjectionClosedOpenComparison
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost EuclideanIsodiametric EuclideanHausdorffLebesgue
  MetricClosedBalls CaratheodoryFamilyReplacement CaratheodoryGeneratorMeasureBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_convex_projection_spherical_bound]: supporting
    convex-cover upper comparison used for Q_t
    in 2.10.35, p. 197. Apply
    the existing closed-cover specification, without
    changing the original open convex definition. *)
Theorem euclidean_convex_projection_spherical_bound (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (@caratheodory_projection_measure R n n A<=
    @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A)%E.
Proof.
apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
  (@positive_closed_metric_balls R (inner_metric_space (@euclidean_inner_productP R n)))
  (closed_convex_euclidean_sets R n) (fun j=>val j) (fun j=>val j)
  (fun j=>hausdorff_diameter_cost n (val j)) (fun j=>projected_volume_gauge n (val j))
  (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) n)
  (@caratheodory_projection_measure R n n) (@spherical_measure_specification R (inner_metric_space (@euclidean_inner_productP R n)) n)
  (@caratheodory_projection_closed_cover_specification R n n (leqnn n)) _ _ A).
- move=> j; exact: projected_volume_gauge_nonnegative (leqnn n).
- move=> j.
  have hclosed := positive_metric_closed_ball_closed (set_valP j).
  have hconv : is_inner_convex (val j).
    have [a [r [hr he]]] := set_valP j.
    have heq : val j=metric_closed_ball a r.
      apply/seteqP; split=> x hx; [exact: (he x).1 hx|exact: (he x).2 hx].
    rewrite heq; exact: inner_metric_closed_ball_convex.
  pose k : closed_convex_euclidean_sets R n :=
    @exist _ (fun C=>C \in [set C : set (inner_metric_space (@euclidean_inner_productP R n)) |
      closed C /\ is_inner_convex C]) (val j) (mem_set (conj hclosed hconv)).
  exists k; split; first by move=> x hx.
  split; first exact: lexx.
  rewrite equal_dimension_projected_volume_gauge.
  exact: lebesgue_isodiametric_bound (positive_metric_closed_ball_nonempty (set_valP j)).
Qed.

(** Source for [euclidean_convex_projection_lebesgue]: supporting
    C^n=L^n consequence of the cost
    comparisons in 2.10.35, p. 197,
    used to identify every Q_t after
    evaluating its full-dimensional gauge. *)
Theorem euclidean_convex_projection_lebesgue (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @caratheodory_projection_measure R n n A=euclidean_lebesgue_measure n A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hh := euclidean_convex_projection_spherical_bound A.
  by rewrite (euclidean_hausdorff_spherical_lebesgue A).2 in hh.
- apply: (measure_bounded_by_caratheodory_generators
    (euclidean_lebesgue_is_measure R n) (caratheodory_projection_measure_specification R n n))=> j.
  by rewrite equal_dimension_projected_volume_gauge.
Qed.
