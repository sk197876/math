(** Federer (1969), 3.2.26, p. 261: replacing a set
    by its measure hull preserves the restricted ball densities.
    Measurable closed balls are exact tests of the hull law,
    including when the original set is not measurable. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureRestriction MeasureHull BorelRegularMeasureUP TopologicalBorel
  MetricClosedBalls MetricDensities PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_hull_metric_ball_density]: supporting
    arbitrary-W case of 3.2.26(1), p. 261. A measure
    hull has the same intersection mass with each closed ball,
    so the actual normalized ball expressions agree. This identity
    asserts no nonzero-denominator claim at radius zero. *)
Lemma measure_hull_metric_ball_density (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (W M:set X) a r:
  is_measure phi ->is_borel_regular_measure phi ->is_measure_hull phi W M ->
  metric_ball_density m (measure_restrict phi W) a r=
    metric_ball_density m (measure_restrict phi M) a r.
Proof.
move=>hPhi hRegular hHull.
have hBall:=borel_regular_borel_measurable hPhi hRegular
  (closed_borel_set (@metric_closed_ball_closed R X a r)).
have hTest:=measure_hull_test hHull hBall.
rewrite /metric_ball_density /measure_restrict (setIC W _) (setIC M _) hTest; by [].
Qed.

(** Source for [measure_hull_upper_metric_density]: supporting
    transfer of the density-one set in 3.2.26(1), p. 261.
    Equality of every positive-radius ball expression gives equality
    of the actual upper metric densities at every base point. *)
Lemma measure_hull_upper_metric_density (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (W M:set X) a:
  is_measure phi ->is_borel_regular_measure phi ->is_measure_hull phi W M ->
  upper_metric_density m (measure_restrict phi W) a=
    upper_metric_density m (measure_restrict phi M) a.
Proof.
move=>hPhi hRegular hHull.
rewrite /upper_metric_density; congr (positive_radius_upper_limit _).
apply:funext=>r; exact:(@measure_hull_metric_ball_density R X phi m W M a r hPhi hRegular hHull).
Qed.
