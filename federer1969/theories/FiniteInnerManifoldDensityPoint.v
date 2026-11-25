(** Federer (1969), 3.3.4, p. 291: positive
    total mass and the almost-everywhere theorem
    3.2.19, p. 256, give an actual density-one
    point on the compact projective manifold.
    This supporting statement works for any
    positive-mass compact class-one submanifold. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric
  FiniteInnerSubmanifoldUP FiniteInnerChartCompact FiniteInnerSubsetDensityTransport
  MetricSubsetBackground HausdorffMeasure MeasureUP MeasureRestriction MeasureAlmostUP
  MeasureAlmostBasic MetricDensities PartialFunctionUP RectifiableTangentPlaneUP RectifiableDensityTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_compact_manifold_density_point]:
    the existence of a density-one point required
    before using homogeneity in Federer 3.3.4,
    p. 291. Compact finite rectifiability and
    actual Euclidean charts discharge 3.2.19;
    positive original mass prevents the entire
    original manifold from being exceptional. *)
Theorem finite_inner_compact_manifold_density_point (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) m
    (S:set (inner_metric_space hB)):
  is_inner_submanifold B m 1%N S ->compact S ->
  (0<@hausdorff_measure R (inner_metric_space hB) m S)%E ->
  exists x:metric_subset S,partial_function_graph
    (metric_density m (@hausdorff_measure R [the metricType R of metric_subset S] m)) x 1%E.
Proof.
move=>[n [e [p [hChart hMan]]]] hCompact hPositive.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose W:set E:=p @` S.
pose H:=@hausdorff_measure R E m.
have [hRect hMeas]:=@finite_inner_chart_compact_manifold_measure R V B hB n m 1%N
  e p S hChart (leqnn 1%N) hMan hCompact.
have hMass:H W=@hausdorff_measure R (inner_metric_space hB) m S.
  exact:(@finite_inner_chart_inverse_hausdorff R V B hB n e p hChart m S).
have hPositiveW:(0<H W)%E by rewrite hMass.
have hAE:=(@federer_3_2_19 R m n W hRect hMeas).1.
have hExists:exists y:E,W y /\
    partial_function_graph (metric_density m (measure_restrict H W)) y 1%E.
  apply:contrapT=>hNone.
  have hBad:W `<=` W `\` [set y|
      partial_function_graph (metric_density m (measure_restrict H W)) y 1%E /\
      RectifiableTangentPlaneUP.is_m_dimensional_approximate_tangent m (measure_restrict H W) y].
    move=>y hy; split=>// hGood; apply:hNone; exists y; by split=>//; exact:hGood.1.
  have hNull:=measure_null_subset (@hausdorff_measure_is_measure R E m) hBad hAE.
  change (H W=0%E) in hNull.
  by move:hPositiveW; rewrite hNull ltxx.
have [y [[x hx hxy] hDensity]]:=hExists.
pose a:metric_subset S:=Sub x (mem_set hx).
exists a; apply/(@finite_inner_subset_density_transport R V B hB n e p S m a 1%E hChart).
by rewrite /a /= hxy.
Qed.
