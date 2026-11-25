(** Federer (1969), 3.2.19, p. 256: the whole theorem for
    a measurable (H^m,m) rectifiable set, with the original Lipschitz
    function represented by its exact partial graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialMetricLipschitz LipschitzUP LipschitzBasic EuclideanPartialLipschitzExtension
  RectifiableSetUP RectifiableTangentPlaneUP RectifiableDensityDifferentiability
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP MeasureApproximateDifferential
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  HausdorffMeasure MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_lipschitz_partial_approximate_differential]:
    the second assertion of Federer 3.2.19, p. 256, including
    the displayed domain of ap Df. The map's actual domain equals W;
    its ambient extension is only an auxiliary existence witness. The
    partial approximate differential has exactly the approximate tangent
    cone as domain by the independently specified laws of 3.2.16. *)
Theorem rectifiable_lipschitz_partial_approximate_differential (R : realType) m n k
    (W : set (R_n R n)) (f : partial_function (R_n R n) (R_n R k)) :
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  partial_function_domain f=W ->
  (exists L, @is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) f L) ->
  let mu := @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  measure_almost_everywhere_on mu W [set w |
    exists d : partial_function (R_n R n) (R_n R k),
      is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
        (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m f w d /\
      partial_function_domain d=measure_approximate_tangent_cone
        (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m w].
Proof.
move=> hRect hW hDom [L hLip] mu.
have [F [hF hGraph]] := euclidean_partial_lipschitz_global_extension hLip.
rewrite hDom in hGraph.
have hFull := rectifiable_density_and_differentiability_global hRect hW (metric_lipschitz_of_bound hF).
have hm := @hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
apply: (measure_null_subset hm _ hFull)=> w [hw hn].
split; first exact hw.
move=> [_ [_ hApprox]]; apply: hn.
rewrite -hGraph in hApprox.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose NY := inner_norm (@euclidean_inner_productP R k).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R k).
pose nu := measure_restrict mu W.
have hmNu := measure_restrict_is_measure hm W.
pose d := @measure_approximate_differential R (R_n R n) (R_n R k) NX NY hNX hNY
  nu m hmNu f w hApprox.
exists d; split.
- split; first exact hApprox.
  exact: (@measure_approximate_differential_graph R (R_n R n) (R_n R k) NX NY hNX hNY
    nu m hmNu f w hApprox).
- exact: (@measure_approximate_differential_domain R (R_n R n) (R_n R k) NX NY hNX hNY
    nu m hmNu f w hApprox).
Qed.

(** Source for [federer_3_2_19]: the entire theorem of Federer
    3.2.19, p. 256. Almost every point of W has H^m
    density one and an m-dimensional approximate tangent vector space.
    Every Lipschitz map with exactly domain W has an approximate
    differential at almost every point, with precisely that tangent
    space as its partial domain. The exceptional set may depend on f,
    as in the printed statement; no simultaneous uncountable intersection
    over all Lipschitz functions is asserted. *)
Theorem federer_3_2_19 (R : realType) m n (W : set (R_n R n)) :
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  let mu := @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  measure_almost_everywhere_on mu W [set w |
    partial_function_graph (metric_density m (measure_restrict mu W)) w 1%E /\
    is_m_dimensional_approximate_tangent m (measure_restrict mu W) w] /\
  forall k (f : partial_function (R_n R n) (R_n R k)),
    partial_function_domain f=W ->
    (exists L, @is_partial_metric_lipschitz_bound R
      (inner_metric_space (@euclidean_inner_productP R n))
      (inner_metric_space (@euclidean_inner_productP R k)) f L) ->
    measure_almost_everywhere_on mu W [set w |
      exists d : partial_function (R_n R n) (R_n R k),
        is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
          (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m f w d /\
        partial_function_domain d=measure_approximate_tangent_cone
          (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m w].
Proof.
move=> hRect hW mu.
split; last by move=> k f; exact: rectifiable_lipschitz_partial_approximate_differential hRect hW.
have hZero : @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R 0)) setT (fun _=>0) 0.
  split; first exact: lexx.
  by move=> x y _ _; rewrite mdistxx mul0r.
have hFull := rectifiable_density_and_differentiability_global hRect hW (metric_lipschitz_of_bound hZero).
apply: (measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m) _ hFull)=> w [hw hn].
split; first exact hw.
by move=> [hDensity [hPlane _]]; apply: hn; split.
Qed.
