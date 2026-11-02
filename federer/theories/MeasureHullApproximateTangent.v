(** Federer (1969), 3.2.25, p. 261: the approximate
    tangent cone is unchanged when an arbitrary set is replaced
    by a measure hull. The directional characterization of
    3.2.16 tests open cones intersected with closed metric balls,
    so only measurable-test equality is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureRestriction MeasureHull
  MeasureApproximateTangentUP MeasureApproximateTangentCriterion ApproximateDirectionConeGeometry
  MetricClosedBalls MetricDensities PositiveRadiusLimits TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_hull_approximate_tangent]: supporting
    initial reduction in Federer 3.2.25, p. 261.
    A measure hull has exactly the same measures of all
    measurable intersections. The open directional-cone criterion
    of 3.2.16, p. 252, therefore gives equality of the
    actual approximate tangent cones at every base point. *)
Theorem measure_hull_approximate_tangent (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (phi:set X->\bar R)
    m (W M:set X) (a:X):
  is_measure phi ->
  (forall A:set (real_norm_metric_space hNX),@borel_set (real_norm_metric_space hNX) A ->
    measure_measurable phi A) ->
  is_measure_hull phi W M ->
  measure_approximate_tangent_cone hNX (measure_restrict phi W) m a=
    measure_approximate_tangent_cone hNX (measure_restrict phi M) m a.
Proof.
move=>hPhi hBorel hHull.
pose T:=real_norm_metric_space hNX.
have hDensity v e:@upper_metric_density R T m
      (measure_restrict (measure_restrict phi W) (approximate_direction_cone NX a v e)) a=
    @upper_metric_density R T m
      (measure_restrict (measure_restrict phi M) (approximate_direction_cone NX a v e)) a.
  congr (positive_radius_upper_limit _).
  apply:funext=>r.
  have hCone:@borel_set T (approximate_direction_cone NX a v e).
    exact:open_borel_set (@approximate_direction_cone_open R X NX hNX a v e).
  have hBall:@borel_set T (metric_closed_ball (a:T) r).
    exact:(@closed_borel_set (real_norm_metric_space hNX) _
      (@metric_closed_ball_closed R (real_norm_metric_space hNX) (a:T) r)).
  have hTest:=measure_hull_test hHull (hBorel _
    (borel_family_binary_intersection (borel_sets_family T) hCone hBall)).
  pose C:=approximate_direction_cone NX a v e.
  pose B:=metric_closed_ball (a:T) r.
  have hWS:W `&` (C `&` B)=(C `&` B) `&` W.
    apply/seteqP; split.
    - by move=>x [hw [hc hb]]; split; first split.
    - by move=>x [[hc hb] hw]; split; last split.
  have hMS:M `&` (C `&` B)=(C `&` B) `&` M.
    apply/seteqP; split.
    - by move=>x [hm [hc hb]]; split; first split.
    - by move=>x [[hc hb] hm]; split; last split.
  rewrite /metric_ball_density /measure_restrict -/C -/B hWS hMS hTest; by [].
apply/seteqP; split=>v.
- move/(@measure_approximate_tangent_directional_criterion R X NX hNX (measure_restrict phi W) m a v (measure_restrict_is_measure hPhi W)).1=>h.
  apply:(@measure_approximate_tangent_directional_criterion R X NX hNX (measure_restrict phi M) m a v (measure_restrict_is_measure hPhi M)).2=>e he.
  by rewrite -(hDensity v e); exact:h e he.
- move/(@measure_approximate_tangent_directional_criterion R X NX hNX (measure_restrict phi M) m a v (measure_restrict_is_measure hPhi M)).1=>h.
  apply:(@measure_approximate_tangent_directional_criterion R X NX hNX (measure_restrict phi W) m a v (measure_restrict_is_measure hPhi W)).2=>e he.
  by rewrite (hDensity v e); exact:h e he.
Qed.
