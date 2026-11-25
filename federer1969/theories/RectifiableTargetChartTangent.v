(** Federer (1969), 3.2.22, p. 259: the
    target-chart differential image agrees almost everywhere
    with the actual approximate tangent plane of Z.
    This is the target application of 3.2.19. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional LipschitzUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure EuclideanLebesgueDimensions
  MeasureApproximateTangentUP RectifiableCompactChartsUP RectifiableCompactChartLaws
  RectifiableDifferentialChartUP RectifiableChartDensityDifferential EuclideanChartAlmostPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_target_chart_tangent_almost]:
    the H^mu target-chart tangent equality used in
    Federer 3.2.22, p. 259. Apply the
    chart proof of 3.2.19 to the identity map
    on Z and pull the exceptional set back to C.
    Uniqueness gives equality for every actual differential
    at each good parameter, without a selected derivative field. *)
Theorem rectifiable_target_chart_tangent_almost (R:realType) mu v
    (lambda:R) (Z:set (R_n R v)) (C:set (R_n R mu)) (gamma:R_n R mu->R_n R v):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda C gamma ->
  gamma @` C `<=` Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z< +oo)%E ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R mu) C [set y|
    forall D:Hom (R_n R mu) (R_n R v),
      has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
        (inner_norm (@euclidean_inner_productP R v)) setT gamma y D ->
      range D=measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R v))
        (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)
        mu (gamma y)].
Proof.
move=>hLambda hChart hCZ hZ hFinite.
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose beta:=@hausdorff_measure R Y mu.
have hb:=@hausdorff_measure_is_measure R Y mu.
have hId:@is_metric_lipschitz R Y Y setT (fun y=>y).
  exists 1; split; first exact:ltr01; split; first exact:ler01.
  by move=>x y _ _; rewrite mul1r.
have hLocal:=rectifiable_chart_density_differential hLambda hChart hCZ hZ hFinite hId.
have hPointAE:measure_almost_everywhere_on beta (gamma @` C)
    [set z|is_rectifiable_differential_chart_point Z C gamma (fun y=>y) z].
  apply:(measure_null_subset hb _ hLocal)=>z [hz hn].
  split; first exact hz; by move=>[_ hPoint]; exact:hn hPoint.
have hParam:=euclidean_chart_almost_pullback (uniform_compact_chart_bilipschitz hChart) hPointAE.
apply:(measure_null_subset (euclidean_lebesgue_is_measure R mu) _ hParam)=>y [hy hNot].
split; first exact hy; move=>hPoint; apply:hNot.
have [a [Ds [H [d [ha [hValue [hInj [hD [hH [hCone [hApx hComp]]]]]]]]]]]:=hPoint.
have hay:a=y:=@uniform_compact_chart_injective R mu v lambda C gamma hChart a y ha hy hValue.
rewrite hay in hD.
move=>D hActual.
have hEq:D=Ds:=@norm_differential_unique R (R_n R mu) (R_n R v)
  (inner_norm (@euclidean_inner_productP R mu)) (inner_norm (@euclidean_inner_productP R v))
  (inner_norm_real_norm (@euclidean_inner_productP R mu))
  (inner_norm_real_norm (@euclidean_inner_productP R v)) setT gamma y D Ds hActual hD.
rewrite hEq; exact:esym hCone.
Qed.
