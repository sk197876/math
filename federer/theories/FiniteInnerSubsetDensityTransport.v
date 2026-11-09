(** Federer (1969), 3.3.4, p. 291: identify
    the actual common Hausdorff density in the
    projective metric carrier with the density of
    its Euclidean chart image. This supporting
    identity uses every original closed ball,
    not a supplied density comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric FiniteInnerChartUP FiniteInnerSubsetBallTransport MetricSubsetBackground
  HausdorffMeasure MeasureRestriction MetricDensities PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_subset_density_transport]:
    the exact density graph transferred from
    3.2.19 into T(U) in Federer 3.3.4,
    p. 291. Equality of the original ball
    masses gives both the upper and lower
    positive-radius limits, including infinite values. *)
Theorem finite_inner_subset_density_transport (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (S:set (inner_metric_space hB)) q (a:metric_subset S) (c: \bar R):
  is_finite_inner_chart B e p ->
  partial_function_graph (metric_density q
    (@hausdorff_measure R [the metricType R of metric_subset S] q)) a c <->
  partial_function_graph (metric_density q
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
      (p @` S))) (p (val a)) c.
Proof.
move=>hChart.
have hFunction:metric_ball_density q
    (@hausdorff_measure R [the metricType R of metric_subset S] q) a=
    metric_ball_density q
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
        (p @` S)) (p (val a)).
  apply:funext=>r; rewrite /metric_ball_density.
  by rewrite (@finite_inner_subset_ball_mass_transport R V B hB n e p S q a r hChart).
by rewrite !metric_density_graph /upper_metric_density /lower_metric_density hFunction.
Qed.
