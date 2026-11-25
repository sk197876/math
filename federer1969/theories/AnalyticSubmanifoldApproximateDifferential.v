(** Federer (1969), 3.2.33, p. 270: the
    intrinsic analytic differential is the original partial
    approximate differential almost everywhere on W. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  RelativeDifferentialUP RelativeAnalyticDifferentialExistence RelativeMeasureApproximateDifferential
  NormAnalyticRelativeUP AnalyticSubmanifoldUP SubmanifoldApproximateTangent
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MetricDensities MetricDensityZeroPowerMass MeasureApproximateTangentUP
  MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness
  HausdorffMeasure RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_relative_approximate_almost]:
    identifying Df and ap Df in Federer 3.2.33,
    p. 270, by 3.2.19 and 3.1.22,
    pp. 256,235. On the actual finite rectifiable
    measurable manifold the approximate tangent equals the
    ordinary tangent almost everywhere. Zero omitted density,
    actual relative existence and approximate uniqueness give
    both directions for every candidate partial differential.
    No off-tangent values are supplied. *)
Theorem analytic_submanifold_relative_approximate_almost (R:realType) n m v
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n m W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  let f:=partial_function_source_restrict W (partial_function_total F) in
  measure_almost_everywhere_on H W [set x|forall d:partial_function (R_n R n) (R_n R v),
    (@has_relative_norm_differential R (R_n R n) (R_n R v)
      (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT W F x d <->
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict H W) m f x d)].
Proof.
move=>hW hF hRect hMeas H f.
pose X:=R_n R n; pose Y:=R_n R v.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R v).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hTangent:=@submanifold_approximate_tangent_almost R n m 1%N W
  (leqnn 1) (analytic_submanifold_class_one hW) hRect hMeas.
have hSelf:W `\` W=set0.
  apply/seteqP; split=>[a [ha hn]|a []]; exact:hn ha.
have hEmpty:H (W `\` W)=0%E by rewrite hSelf; exact:measure_empty hH.
apply:(measure_null_subset hH _ hTangent)=>x [hx hn].
split; first exact hx.
move=>hTan; apply:hn.
have hLoss:=@null_set_metric_density_zero R ([the metricType R of real_norm_metric_space hNX]) m
  H (W `\` W) x hH hEmpty.
have hForward d (hd:@has_relative_norm_differential R X Y NX NY hNX setT W F x d):
    is_measure_approximate_differential NY hNX (measure_restrict H W) m f x d.
  exact:(@relative_differential_is_measure_approximate R X Y NX NY hNX hNY H m W W F x d
    hH (fun y hy=>hy) hLoss hTan hd).
move=>d; split; first by move=>hd; exact:(@hForward d hd).
move=>hApprox.
have [e he]:=relative_analytic_differential_exists hF hx.
have hSame:d=e:=@measure_approximate_differential_unique R X Y NX NY hNX
  (measure_restrict H W) m f x d e hApprox (@hForward e he).
by rewrite hSame.
Qed.
