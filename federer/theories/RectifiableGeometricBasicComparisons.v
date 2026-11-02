(** Federer (1969), 3.2.26, pp. 261–262: the elementary
    comparisons used to finish the equality theorem and to discard
    Hausdorff-null remainders. Derive these from the independently
    specified covering constructions, without assuming the whole
    forward-dependent comparison table of 2.10.6, p. 173. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex InnerClosedBallConvex
  ProjectedVolumeGauge ProjectedExteriorGaugeBound ExteriorMeasureGauge EuclideanIsodiametric
  ProjectionMeasureUP ProjectionMeasure ProjectionClosedOpenComparison
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffSphericalComparison
  MetricClosedBalls CaratheodoryFamilyReplacement CaratheodoryWeightedComparison
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricExponentMonotone
  IntegralGeometricInfinity EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  OrthogonalProjectionProbability ProjectionBeta NonnegativeExtendedExponentNormUP
  NonnegativeExtendedExponentNorm BorelClosedProjection TopologicalBorel BorelCoverCostUP
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_projection_spherical_bound]: supporting
    rough comparison in 3.2.26(2), p. 261. Closed
    balls are closed convex generators. The projection cost is
    bounded by the exterior cost, hence by the normalized
    diameter cost, using 2.10.33–34, p. 197. *)
Theorem convex_projection_spherical_bound (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  @caratheodory_projection_measure R n m A<=
    @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A.
Proof.
apply:(@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
  (@positive_closed_metric_balls R (inner_metric_space (@euclidean_inner_productP R n)))
  (closed_convex_euclidean_sets R n) (fun j=>val j) (fun j=>val j)
  (fun j=>hausdorff_diameter_cost m (val j)) (fun j=>projected_volume_gauge m (val j))
  (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
  (@caratheodory_projection_measure R n m)
  (@spherical_measure_specification R (inner_metric_space (@euclidean_inner_productP R n)) m)
  (@caratheodory_projection_closed_cover_specification R n m hmn) _ _ A).
- move=>j; exact:projected_volume_gauge_nonnegative hmn.
- move=>j.
  have hClosed:=positive_metric_closed_ball_closed (set_valP j).
  have hConv:is_inner_convex (val j).
    have [a [r [hr he]]]:=set_valP j.
    have hEq:val j=metric_closed_ball a r.
      apply/seteqP; split=>x hx; [exact:(he x).1 hx|exact:(he x).2 hx].
    rewrite hEq; exact:inner_metric_closed_ball_convex.
  pose k:closed_convex_euclidean_sets R n:=@exist _
    (fun C=>C \in [set C:set (inner_metric_space (@euclidean_inner_productP R n))|
      closed C /\ is_inner_convex C]) (val j) (mem_set (conj hClosed hConv)).
  exists k; split; first by move=>x hx.
  split; first exact:lexx.
  apply:le_trans (@projected_volume_gauge_exterior_bound R n m (val j)
    (positive_metric_closed_ball_nonempty (set_valP j))) _.
  rewrite /exterior_diameter_cost /hausdorff_diameter_cost /hausdorff_power_cost.
  apply:lee_wpmul2l; last exact:exterior_diameter_metric_power_bound.
  rewrite lee_fin; exact:ltW (hausdorff_normalisation_positive R m).
Qed.

(** Source for [integral_geometric_le_convex]: the vertical
    I_t<=Q_t comparison from 2.10.6, p. 173,
    used in 3.2.26, p. 262. Every open convex
    generator is Borel, with the same cost and diameter. *)
Theorem integral_geometric_le_convex (R:realType) n m (hmn:(m<=n)%N)
    (t: \bar R) (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  1<=t -> @integral_geometric_measure R n m hmn t A<=
    @convex_integral_geometric_measure R n m hmn t A.
Proof.
move=>ht.
apply:(@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
  (open_convex_euclidean_sets R n)
  (@borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j=>val j) (fun j=>val j)
  (fun j=>@integral_geometric_gauge R n m hmn t (val j))
  (fun j=>@integral_geometric_gauge R n m hmn t (val j))
  (@convex_integral_geometric_measure R n m hmn t)
  (@integral_geometric_measure R n m hmn t)
  (@convex_integral_geometric_measure_specification R n m hmn t)
  (@integral_geometric_measure_specification R n m hmn t) _ _ A).
- move=>j; exact:(@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)
    (metric_borel_suslin (set_valP j))).
- move=>j.
  pose k:@borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)):=
    @exist _ (fun C=>C \in [set C|borel_set C]) (val j)
      (mem_set (open_borel_set (set_valP j).1)).
  exists k; split; first by move=>x hx.
  by split; exact:lexx.
Qed.

(** Source for [integral_geometric_infinity_gross_bound]: the
    I_infinity<=G comparison from 2.10.6, p. 173,
    used after 3.2.26(3), p. 262. A pointwise
    bound of projected volumes is an essential bound. Thus the
    two Borel-generator constructions compare directly, including
    unbounded source sets and infinite projected volumes. *)
Theorem integral_geometric_infinity_gross_bound (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  @integral_geometric_measure R n m hmn +oo A<=@gross_measure R n m A.
Proof.
have hCost (S:set (inner_metric_space (@euclidean_inner_productP R n))):
    borel_set S -> @integral_geometric_gauge R n m hmn +oo S<=projected_volume_gauge m S.
  move=>hS.
  have hNorm:=@integral_geometric_gauge_norm_specification R n m hmn +oo (leey 1)
    S (metric_borel_suslin hS).
  rewrite projection_beta_infinity mul1e in hNorm.
  apply:hNorm.1; split; first exact:projected_volume_gauge_nonnegative hmn.
  have hEmpty:[set p:orthogonal_projection_metric_space R n m|
      projected_volume_gauge m S<projected_volume_function S p]=set0.
    apply/seteqP; split=>p; last by [].
    move=>hp.
    have hLe:=projected_volume_gauge_projection_bound S (euclidean_projection_linear_member p).
    by move:hp; rewrite /= ltNge hLe.
  rewrite hEmpty; exact:measure_empty (@theta_star_is_measure R n m hmn).
have hNormalized (j:@borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))):
    @integral_geometric_gauge R n m hmn +oo (val j)<=1%:E*projected_volume_gauge m (val j).
  rewrite mul1e; exact:hCost (set_valP j).
have hBound:=@caratheodory_weighted_generator_comparison R
  (inner_metric_space (@euclidean_inner_productP R n))
  (@borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j=>val j) (fun j=>@integral_geometric_gauge R n m hmn +oo (val j))
  (fun j=>projected_volume_gauge m (val j))
  (@integral_geometric_measure R n m hmn +oo) (@gross_measure R n m) 1
  (@integral_geometric_measure_specification R n m hmn +oo)
  (@gross_measure_specification R n m)
  (fun j=>@integral_geometric_gauge_nonnegative R n m hmn +oo (leey 1) (val j)
    (metric_borel_suslin (set_valP j)))
  (fun j=>@projected_volume_gauge_nonnegative R n m (val j) hmn) ltr01
  hNormalized A.
by rewrite mul1e in hBound.
Qed.

(** Source for [convex_integral_geometric_spherical_rough_bound]:
    supporting null-remainder control in 3.2.26(2),
    p. 261. Monotonicity of beta_t Q_t from
    2.10.5, p. 173, bounds it by Q_infinity=C,
    which is bounded by spherical measure. *)
Theorem convex_integral_geometric_spherical_rough_bound (R:realType) n m
    (hmn:(m<=n)%N) (t: \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  1<=t -> (@projection_beta R n m hmn t)%:E*
    @convex_integral_geometric_measure R n m hmn t A<=
    @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A.
Proof.
move=>ht.
have h:=@convex_integral_geometric_normalized_measure_monotone R n m hmn t +oo A ht (leey t).
rewrite projection_beta_infinity mul1e convex_integral_geometric_infinity in h.
exact:le_trans h (convex_projection_spherical_bound hmn A).
Qed.
